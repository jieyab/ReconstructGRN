
library(bnlearn)
library(grid)
library(Rgraphviz)
library(limma)
library(ROC)
# m_obs: number of samples
# var_noise: variance of Gaussian distributed noise terms
strMCMC <- function(Data,incidence,iterations,step_save, fan.in=nrow(Data)-1, v=1, mu=numeric(nrow(Data)), a=nrow(Data)+2, T_0=diag(0.5,nrow(Data),nrow(Data))){
  n <- nrow(Data)                                # number of nodes
  m <- ncol(Data)                                # number of observations
  
  T_m <- T_0 + (m-1)* cov(t(Data)) + ((v*m)/(v+m))* (mu - rowMeans(Data))%*%t(mu - rowMeans(Data))
  
  L1 <- list()    # incidence matrix
  L2 <- list()    # log BGe score
  ################################################################################
  ##### functions we need in the algorithm
  
  ### calculation of the first ancestor matrix:
  ancestor <- function(incidence){
    incidence1 <- incidence
    incidence2 <- incidence
    k <- 1
    while (k < nrow(incidence)){
      incidence1 <- incidence1%*%incidence
      incidence2 <- incidence2 + incidence1
      k <-k+1
    }
    incidence2[which(incidence2[,]>0)] <- 1
    return(t(incidence2))}
  
  ### function for the computation of c(n, alpha)
  c_function <- function(N,A){
    fact <- numeric(N)
    for (i in 1:N){
      fact[i] <- -lgamma((A+1-i)/2)
    }
    product <- sum(fact) -(A*N/2)*log(2)- (N*(N-1)/4)*log(pi)
    return(product)}
  
  
  top_order <- function(incidence){
    Order <- numeric(n)
    fan_in <- numeric(n)
    no_fan_in <- numeric(0)
    m <- 1
    for (p in 1:n){                                       # number of parent nodes at the beginning
      fan_in[p] <- sum(incidence[,p])
    }
    no_fan_in <- which(fan_in==0)
    while (length(which(Order==0))>0){                    # as long as there is a node without an order
      fan_in[which(incidence[no_fan_in[1],]==1)] <- fan_in[which(incidence[no_fan_in[1],]==1)] - 1
      no_fan_in <- c(no_fan_in, c(which(incidence[no_fan_in[1],]==1),which(fan_in==0))[duplicated(c(which(incidence[no_fan_in[1],]==1),which(fan_in==0)))])
      Order[m] <- no_fan_in[1]
      no_fan_in <- no_fan_in[-1]
      m <- m+1
    }
    return(Order)
  }
  
  
  ### assign the topological order of the descendants of the child
  des_top_order <- function(incidence, ancest1,child){
    top <- top_order(incidence)
    position_child <- which(top==child)
    top_all_after <- top[position_child:n]                # top. order without the "first" nodes
    desc <- which(ancest1[,child]==1)                     # descendants of the child
    inter_step <- c(child,desc,top_all_after)
    des_top <- inter_step[which(duplicated(inter_step))]
    return(des_top)
  }
  
  ################################################################################
  ### computation of the (logarithmizid) BGe Score of the FIRST graph
  P_local_num <- numeric(n)   ###  numerator of the factors
  P_local_den <- numeric(n)   ### denumerator of the factors
  
  for (j in 1:n)  {
    n_nodes <- which(incidence[,j]==1)         # parents of j
    P_local_num[j] <- (-(length(n_nodes)+1)*m/2)*log(2*pi) + ((length(n_nodes)+1)/2)*log(v/(v+m)) + c_function((length(n_nodes)+1),a)-c_function((length(n_nodes)+1),a+m)+ (a/2)*log(det(as.matrix(T_0[sort(c(n_nodes,j)),sort(c(n_nodes,j))])))+ (-(a+m)/2)*log(det(as.matrix(T_m[sort(c(n_nodes,j)),sort(c(n_nodes,j))])))
    if(sum(incidence[,j])>0){          # if j has at least one parent
      P_local_den[j] <- (-(length(n_nodes))*m/2)*log(2*pi) + (length(n_nodes)/2)*log(v/(v+m)) + c_function(length(n_nodes),a)- c_function(length(n_nodes),a+m)+ (a/2)*log(det(as.matrix(T_0[n_nodes,n_nodes])))+ (-(a+m)/2)*log(det(as.matrix(T_m[n_nodes,n_nodes])))
    }
    else{                              # if j has no parents
      P_local_den[j] <- 0
    }
  }
  bge_old <- (sum(P_local_num))-(sum(P_local_den))
  
  # first ancestor matrix
  ancest1 <- ancestor(incidence)
  
  ####### ... the number of neighbour graphs/proposal probability for the FIRST graph
  ### 1.) number of neighbour graphs obtained by edge deletions
  num_deletion <- sum(incidence)
  
  ### 2.) number of neighbour graphs obtained by edge additions    1- E(i,j) - I(i,j) - A(i,j)
  inter_add <- which(matrix(rep(1,n*n),nrow=n) - diag(1,n,n) - incidence - ancest1 >0)
  add <- matrix(numeric(n*n),nrow=n)
  add[inter_add] <- 1
  add[,which(colSums(incidence)>fan.in-1)] <- 0
  num_addition <- sum(add)
  
  ### 3.) number of neighbour graphs obtained by edge reversals    I - (I^t * A)^t
  inter_rev <- which(incidence - t(t(incidence)%*% ancest1)==1)
  re <- matrix(numeric(n*n),nrow=n)
  re[inter_rev] <- 1
  re[which(colSums(incidence)>fan.in-1),] <- 0 # CORRECTED!!!???!!!
  num_reversal <- sum(re)
  
  ##### total number of neighbour graphs:
  total <- sum(num_deletion,num_addition,num_reversal)
  
  ### proposal probability:
  proposal <- 1/total
  
  ############## sampling a new graph (or rather sampling an edge to shift)
  ### sample one of the three single edge operations
  random <- sample(1:total,1)
  
  operation <- 0                           # memorise, if the single edge operation is (will be) an edge reversal
  if (random > total - num_reversal){
    operation <- 1}
  
  #### shifting of the incidence matrix
  incidence_new <- incidence
  
  if (random <= num_deletion){             # if edge deletion was sampled
    if(length(which(incidence>0))>1){
      new_edge <- sample(which(incidence>0),1)} # sample one of the existing edges
    else
    {new_edge <- which(incidence>0)}
    incidence_new[new_edge] <- 0}            # and delete it
  
  if (random > (total - num_reversal)){      # if edge reversal was sampled
    if(num_reversal>1){
      new_edge <- sample(which(re==1),1)}  # sample one of the existing edges where a reversal leads to a valid graph
    else{
      new_edge <- which(re==1)}
    incidence_new[new_edge] <- 0             # delete it
    junk <- matrix(numeric(n*n),nrow=n)      # creating a matrix with all entries zero
    junk[new_edge] <- 1                      # an only a "1" at the entry of the new (reversed) edge
    incidence_new <- incidence_new + t(junk)}# sum the deleted matrix and the "junk-matrix"
  
  if (random <= (total - num_reversal) & random > num_deletion){     # if edge addition was sampled
    if(num_addition>1){
      new_edge <- sample(which(add==1),1)} # sample one of the existing edges where a addition leads to a valid graph
    else{
      new_edge <- which(add==1)}
    incidence_new[new_edge] <- 1             # and add it
  }
  
  
  #################### Updating the ancestor matrix
  
  # creating a matrix with dimensions of the incidence matrix and all entries zero except for the entry of the chosen edge
  help_matrix <- matrix(numeric(n*n),nrow=n)
  help_matrix[new_edge] <- 1
  
  # numbers of the nodes that belong to the shifted egde
  parent <- which(rowSums(help_matrix)==1)
  child <- which(colSums(help_matrix)==1)
  
  ### updating the ancestor matrix (after edge reversal)
  ## edge deletion
  ancestor_new <- ancest1
  if (operation==1){
    ancestor_new[c(child,which(ancest1[,child]==1)),] <- 0           # delete all ancestors of the child and its descendants                                           #
    top_name <- des_top_order(incidence_new, ancest1, child)
    for (d in top_name){
      for(g in which(incidence_new[,d]==1)) {
        ancestor_new[d,c(g,(which(ancestor_new[g,]==1)))] <- 1
      }
    }
    ## edge addition
    anc_parent <- which(ancestor_new[child,]==1)                     # ancestors of the new parent
    des_child <- which(ancestor_new[,parent]==1)                     # descendants of the child
    ancestor_new[c(parent,des_child),c(child,anc_parent)] <- 1
  }
  
  ### updating the ancestor matrix (after edge deletion)
  if (random <= num_deletion){
    ancestor_new[c(child,which(ancest1[,child]==1)),] <- 0           # delete all ancestors of the child and its descendants                                           #
    top_name <- des_top_order(incidence_new, ancest1, child)
    for (d in top_name){
      for(g in which(incidence_new[,d]==1)) {
        ancestor_new[d,c(g,(which(ancestor_new[g,]==1)))] <- 1
      }
    }
  }
  
  # updating the ancestor matrix (after edge addition)
  if (random <= total - num_reversal & random > num_deletion){
    anc_parent <- which(ancest1[parent,]==1)        # ancestors of the new parent
    des_child <- which(ancest1[,child]==1)          # descendants of the child
    ancestor_new[c(child,des_child),c(parent,anc_parent)] <- 1
  }
  
  ####### ... the number of neighbour graphs/proposal probability for the proposed graph
  ### 1.) number of neighbour graphs obtained by edge deletions
  num_deletion_new <- sum(incidence_new)
  
  ### number of neighbour graphs obtained by edge additions    1- E(i,j) - I(i,j) - A(i,j)
  inter_add.new <- which(matrix(rep(1,n*n),nrow=n) - diag(1,n,n) - incidence_new - ancestor_new >0)
  add.new <- matrix(numeric(n*n),nrow=n)
  add.new[inter_add.new] <- 1
  add.new[,which(colSums(incidence_new)>fan.in-1)] <- 0
  num_addition_new <- sum(add.new)
  
  ### number of neighbour graphs obtained by edge reversals    I - (I^t * A)^t
  inter_rev.new <- which(incidence_new - t(t(incidence_new)%*% ancestor_new)==1)
  re.new <- matrix(numeric(n*n),nrow=n)
  re.new[inter_rev.new] <- 1
  re.new[which(colSums(incidence_new)>fan.in-1),] <- 0  # CORRECTED!!!???!!!
  num_reversal_new <- sum(re.new)
  
  ##### total number of neighbour graphs:
  total_new <- sum(num_deletion_new,num_addition_new,num_reversal_new)
  
  ### proposal probability:
  proposal_new <- 1/total_new
  
  ### BGe Score for the new graph
  P_local_num_new <- P_local_num
  P_local_den_new <- P_local_den
  n_nodes_new <- which(incidence_new[,child]==1)
  
  P_local_num_new[child] <- (-(length(n_nodes_new)+1)*m/2)*log(2*pi) + ((length(n_nodes_new)+1)/2)*log(v/(v+m)) + c_function((length(n_nodes_new)+1),a)-c_function((length(n_nodes_new)+1),a+m)+ (a/2)*log(det(as.matrix(T_0[sort(c(n_nodes_new,child)),sort(c(n_nodes_new,child))])))+ (-(a+m)/2)*log(det(as.matrix(T_m[sort(c(n_nodes_new,child)),sort(c(n_nodes_new,child))])))
  
  if(sum(incidence_new[,child])>0){           # if child at least one parent
    P_local_den_new[child] <- (-(length(n_nodes_new))*m/2)*log(2*pi) + (length(n_nodes_new)/2)*log(v/(v+m)) + c_function(length(n_nodes_new),a)- c_function(length(n_nodes_new),a+m)+ (a/2)*log(det(as.matrix(T_0[n_nodes_new,n_nodes_new])))+ (-(a+m)/2)*log(det(as.matrix(T_m[n_nodes_new,n_nodes_new])))
  }
  else{                                       # if child has no parents
    P_local_den_new[child] <- 0
  }
  
  if (operation==1){                          # if single edge operation was an edge reversal
    n_nodesP <- which(incidence_new[,parent]==1)
    P_local_num_new[parent] <- (-(length(n_nodesP)+1)*m/2)*log(2*pi) + ((length(n_nodesP)+1)/2)*log(v/(v+m)) + c_function((length(n_nodesP)+1),a)-c_function((length(n_nodesP)+1),a+m)+ (a/2)*log(det(as.matrix(T_0[sort(c(n_nodesP,parent)),sort(c(n_nodesP,parent))])))+ (-(a+m)/2)*log(det(as.matrix(T_m[sort(c(n_nodesP,parent)),sort(c(n_nodesP,parent))])))
    if(sum(incidence_new[,parent])>0){          # if parent at least one parent
      P_local_den_new[parent] <- (-(length(n_nodesP))*m/2)*log(2*pi) + (length(n_nodesP)/2)*log(v/(v+m)) + c_function(length(n_nodesP),a)- c_function(length(n_nodesP),a+m)+ (a/2)*log(det(as.matrix(T_0[n_nodesP,n_nodesP])))+ (-(a+m)/2)*log(det(as.matrix(T_m[n_nodesP,n_nodesP])))
    }
    else{                                       # if parent has no parents
      P_local_den_new[parent] <- 0
    }
  }
  bge_new <- (sum(P_local_num_new))-(sum(P_local_den_new))
  
  
  L1[[1]] <- incidence                        # initial graph
  L2[[1]] <- bge_old                          # and it`s BGe score
  
  acceptance <- min(1, exp((bge_new + log(proposal_new)) - (bge_old  + log(proposal))))
  rand <- runif(1)
  
  if(acceptance > rand){
    incidence <- incidence_new
    bge_old <- bge_new
    P_local_num <- P_local_num_new
    P_local_den <- P_local_den_new
    proposal <- proposal_new
    ancest1 <- ancestor_new
    total <- total_new
    num_deletion <- num_deletion_new
    num_addition <- num_addition_new
    num_reversal <- num_reversal_new
    add <- add.new
    re <- re.new
  }
  
  ####################################################################################################################################
  #################################################################################
  
  for (z in 2:((iterations/step_save)+1)){
    for (count in 1:step_save){
      
      ############## sampling a new graph (or rather sampling an edge to shift)
      ### sample one of the three single edge operations
      random <- sample(1:total,1)
      
      operation <- 0                            # memorise, if the single edge operation is (will be) an edge reversal
      if (random > total - num_reversal){
        operation <- 1}
      
      #### shifting of the incidence matrix
      incidence_new <- incidence
      
      if (random <= num_deletion){              # if edge deletion was sampled
        if(length(which(incidence>0))>1){
          new_edge <- sample(which(incidence>0),1)} # sample one of the existing edges
        else
        {new_edge <- which(incidence>0)}
        incidence_new[new_edge] <- 0}            # and delete it
      
      if (random > (total - num_reversal)){    # if edge reversal was sampled
        if(num_reversal>1){
          new_edge <- sample(which(re==1),1)}      # sample one of the existing edges where a reversal leads to a valid graph
        else{
          new_edge <- which(re==1)}
        incidence_new[new_edge] <- 0             # delete it
        junk <- matrix(numeric(n*n),nrow=n)      # creating a matrix with all entries zero
        junk[new_edge] <- 1                      # an only a "1" at the entry of the new (reversed) edge
        incidence_new <- incidence_new + t(junk)}# sum the deleted matrix and the "junk-matrix"
      
      if (random <= (total - num_reversal) & random > num_deletion){     # if edge addition was sampled
        if(num_addition>1){
          new_edge <- sample(which(add==1),1)} # sample one of the existing edges where a addition leads to a valid graph
        else{
          new_edge <- which(add==1)}
        incidence_new[new_edge] <- 1             # and add it
      }
      
      
      ### Updating the ancestor matrix
      
      # creating a matrix with dimensions of the incidence matrix and all entries zero except for the entry of the chosen edge
      help_matrix <- matrix(numeric(n*n),nrow=n)
      help_matrix[new_edge] <- 1
      
      # numbers of the nodes that belong to the shifted egde
      parent <- which(rowSums(help_matrix)==1)
      child <- which(colSums(help_matrix)==1)
      
      ### updating the ancestor matrix (after edge reversal)
      ## edge deletion
      ancestor_new <- ancest1
      if (operation==1){
        ancestor_new[c(child,which(ancest1[,child]==1)),] <- 0   # delete all ancestors of the child and its descendants                                           #
        
        top_name <- des_top_order(incidence_new, ancest1, child)
        for (d in top_name){
          for(g in which(incidence_new[,d]==1)) {
            ancestor_new[d,c(g,(which(ancestor_new[g,]==1)))] <- 1
          }
        }
        
        anc_parent <- which(ancestor_new[child,]==1)          # ancestors of the new parent
        des_child <- which(ancestor_new[,parent]==1)          # descendants of the child
        ancestor_new[c(parent,des_child),c(child,anc_parent)] <- 1
      }
      
      ### updating the ancestor matrix (after edge deletion)
      if (random <= num_deletion){
        ancestor_new[c(child,which(ancest1[,child]==1)),] <- 0   # delete all ancestors of the child and its descendants                                           #
        top_name <- des_top_order(incidence_new, ancest1, child)
        for (d in top_name){
          for(g in which(incidence_new[,d]==1)) {
            ancestor_new[d,c(g,(which(ancestor_new[g,]==1)))] <- 1
          }
        }
      }
      
      # updating the ancestor matrix (after edge addition)
      if (random <= total - num_reversal & random > num_deletion){
        anc_parent <- which(ancest1[parent,]==1)             # ancestors of the new parent
        des_child <- which(ancest1[,child]==1)               # descendants of the child
        ancestor_new[c(child,des_child),c(parent,anc_parent)] <- 1
      }
      
      ####### ... the number of neighbour graphs/proposal probability for the proposed graph
      ### 1.) number of neighbour graphs obtained by edge deletions
      num_deletion_new <- sum(incidence_new)
      
      ### number of neighbour graphs obtained by edge additions    1- E(i,j) - I(i,j) - A(i,j)
      inter_add.new <- which(matrix(rep(1,n*n),nrow=n) - diag(1,n,n) - incidence_new - ancestor_new >0)
      add.new <- matrix(numeric(n*n),nrow=n)
      add.new[inter_add.new] <- 1
      add.new[,which(colSums(incidence_new)>fan.in-1)] <- 0
      num_addition_new <- sum(add.new)
      
      ### number of neighbour graphs obtained by edge reversals    I - (I^t * A)^t
      inter_rev.new<- which(incidence_new - t(t(incidence_new)%*% ancestor_new)==1)
      re.new <- matrix(numeric(n*n),nrow=n)
      re.new[inter_rev.new] <- 1
      re.new[,which(colSums(incidence_new)>fan.in-1)] <- 0
      num_reversal_new <- sum(re.new)
      
      ##### total number of neighbour graphs:
      total_new <- sum(num_deletion_new, num_addition_new, num_reversal_new)
      
      ### proposal probability:
      proposal_new <- 1/total_new
      
      ### BGe Score for the new graph
      P_local_num_new <- P_local_num
      P_local_den_new <- P_local_den
      n_nodes_new <- which(incidence_new[,child]==1)
      
      P_local_num_new[child] <- (-(length(n_nodes_new)+1)*m/2)*log(2*pi) + ((length(n_nodes_new)+1)/2)*log(v/(v+m)) + c_function((length(n_nodes_new)+1),a)-c_function((length(n_nodes_new)+1),a+m)+ (a/2)*log(det(as.matrix(T_0[sort(c(n_nodes_new,child)),sort(c(n_nodes_new,child))])))+ (-(a+m)/2)*log(det(as.matrix(T_m[sort(c(n_nodes_new,child)),sort(c(n_nodes_new,child))])))
      
      if(sum(incidence_new[,child])>0){       # if child at least one parent
        P_local_den_new[child] <- (-(length(n_nodes_new))*m/2)*log(2*pi) + (length(n_nodes_new)/2)*log(v/(v+m)) + c_function(length(n_nodes_new),a)- c_function(length(n_nodes_new),a+m)+ (a/2)*log(det(as.matrix(T_0[n_nodes_new,n_nodes_new])))+ (-(a+m)/2)*log(det(as.matrix(T_m[n_nodes_new,n_nodes_new])))
      }
      else{                                   # if child has no parents
        P_local_den_new[child] <- 0
      }
      
      if (operation==1){                      # if single edge operation was an edge reversal
        n_nodesP <- which(incidence_new[,parent]==1)
        P_local_num_new[parent] <- (-(length(n_nodesP)+1)*m/2)*log(2*pi) + ((length(n_nodesP)+1)/2)*log(v/(v+m)) + c_function((length(n_nodesP)+1),a)-c_function((length(n_nodesP)+1),a+m)+ (a/2)*log(det(as.matrix(T_0[sort(c(n_nodesP,parent)),sort(c(n_nodesP,parent))])))+ (-(a+m)/2)*log(det(as.matrix(T_m[sort(c(n_nodesP,parent)),sort(c(n_nodesP,parent))])))
        if(sum(incidence_new[,parent])>0){      # if parent at least one parent
          P_local_den_new[parent] <- (-(length(n_nodesP))*m/2)*log(2*pi) + (length(n_nodesP)/2)*log(v/(v+m)) + c_function(length(n_nodesP),a)- c_function(length(n_nodesP),a+m)+ (a/2)*log(det(as.matrix(T_0[n_nodesP,n_nodesP])))+ (-(a+m)/2)*log(det(as.matrix(T_m[n_nodesP,n_nodesP])))
        }
        else{                                   # if parent has no parents
          P_local_den_new[parent] <- 0
        }
      }
      bge_new <- (sum(P_local_num_new))-(sum(P_local_den_new))
      
      acceptance <- min(1, exp((bge_new +log(proposal_new)) - (bge_old +log(proposal))))
      rand <- runif(1)
      
      if(acceptance > rand){
        incidence <- incidence_new
        bge_old <- bge_new
        P_local_num <- P_local_num_new
        P_local_den <- P_local_den_new
        proposal <- proposal_new
        ancest1 <- ancestor_new
        total <- total_new
        num_deletion <- num_deletion_new
        num_addition <- num_addition_new
        num_reversal <- num_reversal_new
        add <- add.new
        re <- re.new
      }
    }
    
    L1[[z]] <- incidence
    L2[[z]] <- bge_old
  }
  return(list(L1,L2))
}

################################################################################

child <- function(edges,n){         # input: the numbers of the edges in the incidence matrix and the number of nodes
  p <- ceiling(edges/n)
  return(p)
}

parent <- function(edges,n){
  ch <- edges + n - child(edges,n)*n
  return(ch)
}


top_order <- function(incidence){
  n <- nrow(incidence)
  Order <- numeric(n)
  fan_in <- numeric(n)
  no_fan_in <- numeric(0)
  m <- 1
  for (p in 1:n){                                       # number of parent nodes at the beginning
    fan_in[p] <- sum(incidence[,p])
  }
  no_fan_in <- which(fan_in==0)
  while (length(which(Order==0))>0){                    # as long as there is a node without an order
    fan_in[which(incidence[no_fan_in[1],]==1)] <- fan_in[which(incidence[no_fan_in[1],]==1)] - 1
    no_fan_in <- c(no_fan_in, c(which(incidence[no_fan_in[1],]==1),which(fan_in==0))[duplicated(c(which(incidence[no_fan_in[1],]==1),which(fan_in==0)))])
    Order[m] <- no_fan_in[1]
    no_fan_in <- no_fan_in[-1]
    m <- m+1
  }
  return(Order)
}

################################################################################
order.edges <- function(incidence){
  top.order <- top_order(incidence)
  n <- length(top.order)
  edges <- which(incidence!=0)
  children <- child(edges,n)
  parents <- parent(edges,n)
  m <- length(edges)
  ordered_edges  <- numeric(m)
  incidence_n <- incidence
  tog <- matrix(c(edges,parents,children,ordered_edges),ncol=4, byrow=FALSE)
  k <- 1
  while(any(tog[,4]==0)){
    node1 <- top.order[which(colSums(incidence_n[,top.order])>0)][1]    # first node in top. order that has at least one parent
    par1<- tog[which(tog[,3]==node1),2]                # find the parents of  first child in the top. order that has an unordered edge incident into it
    g <- par1[which(par1>0)]
    f1 <- numeric(length(g))
    for (i in 1:length(g)){
      f1[i] <- which(top.order==g[i])
    }
    par2 <- g[which.max(f1)]                           # find the highest ordered node that has an edge leading into node1
    tog[which(tog[,2]==par2 & tog[,3]==node1),4] <- k
    k <- k + 1
    incidence_n[tog[which(tog[,2]==par2 & tog[,3]==node1),1]] <- 0     # delete the edge in the "incidence" matrix
    tog[which(tog[,2]==par2 & tog[,3]==node1),2] <- 0
  }
  to <- matrix(c(edges,parents,children,tog[,4]),ncol=4,byrow=FALSE)
  return(to)                                          # return the whole matrix, the order is the fourth column
}

#################################################################################
### DAG-to-CPDAG algorithm
# +1 if the edge is "compelled"
#   -1 if the edge is "reversible"
#######################################################################
cpdag <- function(incidence){
  z <- order.edges(incidence)
  new_mat <- cbind(z,numeric(nrow(z)))    # edges, parents, children, order, zeros
  n_mat <- new_mat[order(new_mat[,4]),]   # sort the edges by its order
  vec <- numeric(nrow(z))
  while(any(vec==0)){                                  # while there are unlabeled edges            l.3
    if (length(vec)>1){                                  # if there are at least 2 edges
      first <- which(n_mat[,5]==0)[1]                    # first EDGE that ist labeled "unknown" (0)  l.4
      parent1 <- n_mat[first,2]                          # x   parent NODE
      child1 <- n_mat[first,3]                           # y   child NODE
      comp1 <- n_mat[which(n_mat[,3]==parent1 & n_mat[,5]==1),2]      # w NODES that have an edge incident into the parent labeled compelled)
    }
    if (length(vec)==1){
      first <- which(n_mat[5]==0)                      # first edge that ist labeled "unknown" (0)
      parent1 <- n_mat[2]                             # x   parent
      child1 <- n_mat[3]                              # y   child
      comp1 <- numeric(0)
    }
    for (j in comp1){                                   #                                            l.5
      if (incidence[j,child1]==0){                     # if w is not a parent of the child          l.6
        n_mat[first,5] <- 1                             # label x -> y compelled                     l.7
        n_mat[which(n_mat[,3]==child1),5] <- 1          # label every edge incident into y compelled l.7
        vec[first] <- 1
        vec[which(n_mat[,3]==child1)] <- 1
        break
      }
      if (incidence[j,child1]!=0)    {
        n_mat[which(n_mat[,2]==j & n_mat[,3]==child1),5] <- 1  # label w -> y compelled                l.10
        vec[which(n_mat[,2]==j & n_mat[,3]==child1)] <- 1
      }
    }
    if (length(vec)>1){
      if(n_mat[first,5]==0){
        
        moep <- n_mat[which(n_mat[,3]==child1 & n_mat[,2]!=parent1),2]      # other parents of the child
        if(length(moep)>0){                              #                     l.11
          for(o in moep){
            if(incidence[o,parent1]==0){
              vec[first] <- 1
              vec[which(n_mat[,3]==child1 & n_mat[,5]==0)] <- 1
              n_mat[first,5] <- 1                                     # label x -> y compelled
              n_mat[which(n_mat[,3]==child1 & n_mat[,5]==0),5] <- 1   # label all "unknown" edges incident into y compelled
              break
            }
            if(all(incidence[moep,parent1]!=0)){
              vec[first] <- -1
              vec[which(n_mat[,3]==child1 & n_mat[,5]==0)] <- -1
              n_mat[first,5] <- -1                                    # label x -> y reversible
              n_mat[which(n_mat[,3]==child1 & n_mat[,5]==0),5] <- -1  # label all "unknown" edges incident into y reversible
            }
          }
        }
        if(length(moep)==0){
          vec[first] <- -1
          vec[which(n_mat[,3]==child1 & n_mat[,5]==0)] <- -1
          n_mat[first,5] <- -1                                    # label x -> y reversible
          n_mat[which(n_mat[,3]==child1 & n_mat[,5]==0),5] <- -1  # label all "unknown" edges incident into y reversible
        }
      }
    }
    if (length(vec)==1){
      n_mat[5] <- -1                                    # label x -> y reversible
      vec <- -1
    }
  }
  return(n_mat)
}


################################################################################

cpdag_list <- function(list.inc,E){    # E: end of burnIn phase
  L <- list()
  G <- list()
  nodes <- dim(list.inc[[1]])[1]
  mat.sum <- matrix(numeric(nodes*nodes),nrow=nodes)
  for (i in E:length(list.inc)){
    newlist <- list.inc[[i]]
    k <- cpdag(newlist)
    dummy <- matrix(numeric(nodes*nodes),nrow=nodes)
    if(length(nrow(k))!=0){
      dummy[k[,1]] <- k[,5]
      L[[i]] <- dummy
    }
    if(length(nrow(k))==0 && length(k)>0){
      dummy[k[1]] <- k[5]
      L[[i]] <- dummy
    }
    mat.com <-matrix(numeric(nodes*nodes),nrow=nodes)
    mat.re <- matrix(numeric(nodes*nodes),nrow=nodes)
    com <- which(L[[i]]>0)
    re <- which(L[[i]]<0)
    mat.com[com] <- 1
    mat.re[re] <- 1
    mat <- mat.com + mat.re + t(mat.re)
    G[[i]] <- mat
    mat.sum <- mat.sum + mat
  }
  return(list(L,G, (mat.sum/(length(list.inc)- E+1))))
}


## AUROC

#true network
make_true_Net <- function(){
  
  NETWORK <- matrix(numeric(11*11),11,11)
  
  # 1. pip3
  
  # 2. plcg
  NETWORK[1,2] <- 1
  
  # 3. pip2
  NETWORK[1,3] <- 1
  NETWORK[2,3] <- 1
  
  # 4. pkc
  NETWORK[2,4] <- 1
  NETWORK[3,4] <- 1
  
  # 5. pka
  NETWORK[4,5] <- 1
  
  # 6. jnk
  NETWORK[4,6]  <- 1
  NETWORK[5,6]  <- 1
  
  # 7. p3B
  NETWORK[4,7]  <- 1
  NETWORK[5,7]  <- 1
  
  # 8. raf
  NETWORK[4,8]  <- 1
  NETWORK[5,8]  <- 1
  
  # 9. mek
  NETWORK[4,9]  <- 1
  NETWORK[5,9]  <- 1
  NETWORK[8,9]  <- 1
  
  # 10. erk
  NETWORK[5,10]  <- 1
  NETWORK[9,10]  <- 1
  
  # 11. akt
  NETWORK[1,11]  <- 1
  NETWORK[5,11]  <- 1
  NETWORK[10,11]  <- 1
  
  return(NETWORK)
}

#extract CPDAG
extract_cpdag_of_dag <- function(true_incidence){    
  
  L <- list()
  
  nodes <- dim(true_incidence)[1]
  
  k <- cpdag(true_incidence)
  
  
  dummy <- matrix(numeric(nodes*nodes),nrow=nodes)
  
  if(length(nrow(k))!=0){
    dummy[k[,1]] <- k[,5]
    L <- dummy
  }
  
  if(length(nrow(k))==0 && length(k)>0){
    dummy[k[1]] <- k[5]
    L <- dummy
  }
  
  mat.com <- matrix(numeric(nodes*nodes),nrow=nodes)
  mat.re  <- matrix(numeric(nodes*nodes),nrow=nodes)
  
  com <- which(L>0)
  re  <- which(L<0)
  
  mat.com[com] <- 1
  mat.re[re] <- 1
  mat <- mat.com + mat.re + t(mat.re)
  
  return(mat)
}

# ROC
library(limma)
library(ROC)

draw_ROC <- function(postP, trueEdges, steps=0.01){
  
  
  n1 <- numeric(0)
  for(i in 1:dim(postP)[1]){
    for(j in 1:dim(postP)[2]){
      if (abs(i-j)>0){
        n1 <- c(n1, postP[i,j])
      }
    }
  }
  
  n2 <- numeric(0)
  for(i in 1:dim(trueEdges)[1]){
    for(j in 1:dim(trueEdges)[2]){
      if (abs(i-j)>0){     
        n2 <- c(n2, trueEdges[i,j])
      }
    }
  }
  
  sp <- sort(n1)         # posterior probabilities
  st <- n2[order(n1)]    # true ordered by posterior probabilities
  
  rocc.obj <- rocdemo.sca(n2, n1, rule=NULL, cutpts=NA)#seq(0,1,steps))
  
  return(list(plot((1-rocc.obj@"spec"), rocc.obj@"sens", type="l",las=1, xlab="1 - specificity", ylab="sensitivity", main='ROC curve'), abline(0,1, lty=2)))
  
  
}

compute_AUROC <- function(postP, trueEdges, steps=0.01){
  
  n1 <- numeric(0)
  for(i in 1:dim(postP)[1]){
    for(j in 1:dim(postP)[2]){
      if (abs(i-j)>0){
        n1 <- c(n1, postP[i,j])
      }
    }
  }
  
  n2 <- numeric(0)
  for(i in 1:dim(trueEdges)[1]){
    for(j in 1:dim(trueEdges)[2]){
      if (abs(i-j)>0){     
        n2 <- c(n2, trueEdges[i,j])
      }
    }
  }
  
  
  sp <- sort(n1)         # posterior probabilities
  st <- n2[order(n1)]    # true ordered by posterior probabilities
  
  rocc.obj <- rocdemo.sca(n2, n1, rule=NULL, cutpts=NA)#seq(0,1,steps))
  
  return(auROC(st,sp))
  
}
#make test function 
make_test_Data <- function(m_obs, var_noise){
  edges <- 20
  a1 <- runif(edges,0.5,2)
  a2 <- sample(c(-1,1),edges, replace=TRUE)
  a <- a1*a2    # vector with regression coefficients for the 20 edges
  
  # 1. pip3
  x_pip3 <- rnorm(m_obs, sd=1)
  pip3 <- (x_pip3 - mean(x_pip3))/sd(x_pip3)
  
  # 2. plcg
  x_plcg <- a[1]* pip3 + rnorm(m_obs, sd=sqrt(var_noise))
  plcg <- (x_plcg - mean(x_plcg))/sd(x_plcg)
  
  # 3. pip2
  x_pip2 <- a[2]* pip3 + a[3]*plcg + rnorm(m_obs, sd=sqrt(var_noise))
  pip2 <- (x_pip2 - mean(x_pip2))/sd(x_pip2)
  
  # 4. pkc
  x_pkc <- a[4]* pip2 + a[5]*plcg + rnorm(m_obs, sd=sqrt(var_noise))
  pkc  <- (x_pkc - mean(x_pkc))/sd(x_pkc)
  
  # 5. pka
  x_pka <- a[6]* pkc + rnorm(m_obs, sd=sqrt(var_noise))
  pka  <- (x_pka - mean(x_pka))/sd(x_pka)
  
  # 6. jnk
  x_jnk <- a[7]* pkc + a[8]* pka + rnorm(m_obs, sd=sqrt(var_noise))
  jnk  <- (x_jnk - mean(x_jnk))/sd(x_jnk)
  
  # 7. p38
  x_p38 <- a[9]* pkc + a[10]* pka + rnorm(m_obs, sd=sqrt(var_noise))
  p38  <- (x_p38 - mean(x_p38))/sd(x_p38)
  
  # 8. raf
  x_raf <- a[11]* pkc + a[12]* pka + rnorm(m_obs, sd=sqrt(var_noise))
  raf  <- (x_raf - mean(x_raf))/sd(x_raf)
  
  # 9. mek
  x_mek <- a[13]* pkc + a[14]* pka + a[15]* raf + rnorm(m_obs, sd=sqrt(var_noise))        
  mek  <- (x_mek - mean(x_mek))/sd(x_mek)
  
  # 10. erk
  x_erk <- a[16]* pka + a[17]* mek + rnorm(m_obs, sd=sqrt(var_noise))
  erk  <- (x_erk - mean(x_erk))/sd(x_erk)
  
  # 11. akt
  x_akt <- a[18]* pip3 + a[19]* pka + a[20]* erk + rnorm(m_obs, sd=sqrt(var_noise))
  akt  <- (x_akt - mean(x_akt))/sd(x_akt)    
  
  daten <- cbind(pip3, plcg, pip2, pkc, pka, jnk, p38, raf, mek, erk, akt)
  
  return(t(daten))
}

### generate Gaussian Synthetic data for RAF
m = 900 # Set sample size 900
Data.sim1 <- make_test_Data(m,1)
Data.sim2 <- make_test_Data(m,1)
Data.sim3 <- make_test_Data(m,1)
##########################################################################################################
################################Part1  ALgorithm comparisons for RAF network using continuous data ###########
####### generate true DAG for directed graoh
true_Net <- make_true_Net() 
true_Cpdag <- extract_cpdag_of_dag(true_Net) 
####### generate true DAG for undirectured graph
true_Net_undirected <- true_Net + t(true_Net)

##################################### 1. Network reconstruction for RAF observational data
# data inspecting for real observational data
setwd('/Users/jieyab/Downloads')
sachs <- read.table("sachs.data.txt", header = TRUE)
head(sachs)
#inspect the normal distribution of data
par(mar=c(2,2,2,2))
par(mfrow=c(2,3))
hist(sachs$Raf)
hist(sachs$Mek)
hist(sachs$Plcg)

# log transform data
lsachs <- log(sachs)
head(lsachs)
hist(lsachs$Raf)
hist(lsachs$Mek)
hist(lsachs$Plcg)

#####################1.1 MH MCMC Bayesian structural learning for observational data #################
#MCMC for real data
I <- matrix (0,nrow =11, ncol = 11)
col.order<-c("PIP3","Plcg","PIP2","PKC","PKA","Jnk","P38","Raf","Mek","Erk","Akt")
#reorder and Tranform data matrix to meet the form for function input
lsachs<-lsachs[,col.order] 
names <- rownames(Data.sim1)
colnames(lsachs) <- names
lsachs.mcmc <- t(lsachs)
head(lsachs.mcmc)

# run strMCMC algorithms for log transformed sachs observational data three times and average the AUROC
# MCMC run1
start.time1 <- Sys.time() # the system time when the similation starts
run_real1 <- strMCMC(lsachs.mcmc,I,100000,100,11)
end.time1 <- Sys.time() #the system time when the similation ends
time.taken1 <- end.time1 - start.time1 # The computational costs
time.taken1
L1_1<- (run_real1[[1]])    # incidence matrix
L2_1<- (run_real1[[2]])    # BGe
list1 <- cpdag_list(L1_1,500)
edges_mat_1 <- list1[[3]]
AUC_1 <- compute_AUROC(edges_mat_1,true_Cpdag)
AUC_1
# MCMC run2
start.time2 <- Sys.time() # the system time when the similation starts
run_real2 <- strMCMC(lsachs.mcmc,I,100000,100,11)
end.time2 <- Sys.time() #the system time when the similation ends
time.taken2 <- end.time2 - start.time2 # The computational costs
time.taken2
L1_2<- (run_real2[[1]])    # incidence matrix
L2_2<- (run_real2[[2]])    # BGe
list2 <- cpdag_list(L1_2,500)
edges_mat_2 <- list2[[3]]
AUC_2 <- compute_AUROC(edges_mat_2,true_Cpdag)
AUC_2
# MCMC run3
start.time3 <- Sys.time() # the system time when the similation starts
run_real3 <- strMCMC(lsachs.mcmc,I,100000,100,11)
end.time3 <- Sys.time() #the system time when the similation ends
time.taken3 <- end.time3 - start.time3 # The computational costs
time.taken3
L1_3<- (run_real3[[1]])    # incidence matrix
L2_3<- (run_real3[[2]])    # BGe
list3 <- cpdag_list(L1_3,500)
edges_mat_3 <- list3[[3]]
AUC_3 <- compute_AUROC(edges_mat_3,true_Cpdag)
AUC_3
#averaging AUROC values
AUC_real <- c(AUC_1,AUC_2,AUC_3)
AUC_real_avg <- mean(AUC_real)
AUC_real_sd <- sd(AUC_real)
timeMCMC.real <- (time.taken1+time.taken2+time.taken3)/3
#undirected score for MCMC DAG result to compare with constraint algorithms
n   <- length(run_real1[[1]])
SCORES_undirected<- matrix(0,11,11)
for (i in (n/2):n){
  SCORES_undirected <- (SCORES_undirected + run_real1[[1]][[i]] + t(run_real1[[1]][[i]]))}
SCORES_undirected<- (SCORES_undirected/n)*2
AUROC_undirected_real1 <- compute_AUROC(SCORES_undirected,true_Net_undirected)

n   <- length(run_real2[[1]])
SCORES_undirected<- matrix(0,11,11)
for (i in (n/2):n){
  SCORES_undirected <- (SCORES_undirected + run_real2[[1]][[i]] + t(run_real2[[1]][[i]]))}
SCORES_undirected<- (SCORES_undirected/n)*2
AUROC_undirected_real2 <- compute_AUROC(SCORES_undirected,true_Net_undirected)

n   <- length(run_real3[[1]])
SCORES_undirected<- matrix(0,11,11)
for (i in (n/2):n){
  SCORES_undirected <- (SCORES_undirected + run_real3[[1]][[i]] + t(run_real3[[1]][[i]]))}
SCORES_undirected<- (SCORES_undirected/n)*2
AUROC_undirected_real3 <- compute_AUROC(SCORES_undirected,true_Net_undirected)
AUROC_undirected_real <- c(AUROC_undirected_real1,AUROC_undirected_real2,AUROC_undirected_real3)
AUROC_undirected_avg <- mean(AUROC_undirected_real)
AUROC_undirected_sd <- sd(AUROC_undirected_real)

##### 1.2 bayesian learning algorithms functions in bnlearn packages for observational continuous RAF data
##1.2.1 score based algorithms for observational RAF data
start.time <- Sys.time() 
dag.hc.bic <- hc(lsachs, score = "bic-g",start = random.graph(names(lsachs)))
end.time <- Sys.time() #the system time when the similation ends
time.taken <- end.time - start.time # The computational costs
time.taken
dag.hc.bge <- hc(lsachs, score = "bge",start = random.graph(names(lsachs)))
dag.tabu.bic <- tabu(lsachs, score = "bic-g",start = random.graph(names(lsachs)))
dag.tabu.bge <- tabu(lsachs, score = "bge",start = random.graph(names(lsachs)))
#obtaining incidence matrix and #comput AUROC
dag.hc.bic.matrix <- amat(dag.hc.bic)
AUROC_hcbic <- compute_AUROC(dag.hc.bic.matrix,true_Cpdag)
dag.hc.bge.matrix <- amat(dag.hc.bge)
AUROC_hcbge <- compute_AUROC(dag.hc.bge.matrix,true_Cpdag)
dag.tabu.bic.matrix <- amat(dag.tabu.bic)
AUROC_tabubic <- compute_AUROC(dag.tabu.bic.matrix,true_Cpdag)
dag.tabu.bge.matrix <- amat(dag.tabu.bge)
AUROC_tabubge <- compute_AUROC(dag.tabu.bge.matrix,true_Cpdag)
AUROC_hcbic
AUROC_hcbge
AUROC_tabubic 
AUROC_tabubge

##1.2.2 hybrid algorithm for observational RAF data
dag.mmhc <- mmhc(lsachs)
dag.rsmax <- rsmax2(lsachs, restrict = "mmpc", maximize = "hc",start = random.graph(names(lsachs)))
dag.rsmax2 <- rsmax2(lsachs, restrict = "si.hiton.pc",  maximize = "tabu",start = random.graph(names(lsachs)))
#obtaining incidence matrix and #comput AUROC
dag.mmhc.matrix <- amat(dag.mmhc)
AUROC_mmhc <- compute_AUROC(dag.mmhc.matrix,true_Cpdag)
dag.rsmax.matrix <- amat(dag.rsmax)
AUROC_rsmax <- compute_AUROC(dag.rsmax.matrix,true_Cpdag)
dag.rsmax2.matrix <- amat(dag.rsmax2)
AUROC_rsmax2 <- compute_AUROC(dag.rsmax2.matrix,true_Cpdag)
AUROC_mmhc
AUROC_rsmax
AUROC_rsmax2

##1.2.3 constraint based algorithm for observational RAF data
###Grow-Shrink 
net1 <- gs(lsachs)
net1Matrix <- amat(net1) #obtaining incidence matrix
AUC_net1 <- compute_AUROC(net1Matrix,true_Net_undirected)
AUC_net1
##Incremental Association Markov Blanket
net2 <- iamb(lsachs)
net2Matrix <- amat(net2)
AUC_net2 <- compute_AUROC(net2Matrix,true_Net_undirected)
AUC_net2
#Fast Incremental Association (fast.iamb):
net3 <- fast.iamb(lsachs)
net3Matrix <- amat(net3)
AUC_net3 <- compute_AUROC(net3Matrix,true_Net_undirected)
AUC_net3
#Interleaved Incremental Association (inter.iamb):
net4 <- inter.iamb(lsachs)
net4Matrix <- amat(net4)
AUC_net4 <- compute_AUROC(net4Matrix,true_Net_undirected)
AUC_net4
#Max-Min Parents and Children (mmpc):
net5 <- mmpc(lsachs)
net5Matrix <- amat(net5)
#true_Net2 <- true_Net + t(true_Net)
AUC_net5 <- compute_AUROC(net5Matrix,true_Net_undirected)
AUC_net5

################### 2. ALgorithm comparison for Gaussian simulated dataset for RAF
# 2.1 run strMCMC algorithms for synthetic data three times and average the AUROCI 
start.time1a <- Sys.time() # the system time when the similation starts
run1_a <- strMCMC(Data.sim1,I,100000,100,11)
end.time1a <- Sys.time() #the system time when the similation ends
time.taken1a <- end.time1a - start.time1a # The computational costs
time.taken1a
L1_1a<- (run1_a[[1]])    # incidence matrix
L2_1a<- (run1_a[[2]])    # BGe
list1a <- cpdag_list(L1_1a,500)
edges_mat_1a <- list1a[[3]]
AUC_1a <- compute_AUROC(edges_mat_1a,true_Cpdag)
AUC_1a

start.time2a <- Sys.time()
run2_a <- strMCMC(Data.sim2,I,100000,100,11)
end.time2a <- Sys.time()
time.taken2a <- end.time2a - start.time2a
time.taken2a
L1_2a<- (run2_a[[1]])    
L2_2a<- (run2_a[[2]]) 
list2a <- cpdag_list(L1_2a,500)
edges_mat_2a <- list2a[[3]]
AUC_2a <- compute_AUROC(edges_mat_2a,true_Cpdag)
AUC_2a

start.time3a <- Sys.time()
run3_a <- strMCMC(Data.sim3,I,100000,100,11)
end.time3a <- Sys.time()
time.taken3a <- end.time3a - start.time3a
time.taken3a
L1_3a<-(run3_a[[1]])    
L2_3a<-(run3_a[[2]]) 
list3a <- cpdag_list(L1_3a,500)
edges_mat_3a <- list3a[[3]]
AUC_3a <- compute_AUROC(edges_mat_3a,true_Cpdag)
AUC_3a

AUC_sim <- c(AUC_1a,AUC_2a,AUC_3a)
AUC_sim_avg <- mean(AUC_sim)
AUC_sim_sd <-sd(AUC_sim)
AUC_sim_avg
AUC_sim_sd
time.taken.sim <- (time.taken1a+time.taken2a+time.taken3a)/3
time.taken.sim

#AUROC score for undirected graph
n   <- length(run1_a[[1]])
SCORES_undirectedsim <- matrix(0,11,11)
for (i in (n/2):n){
  SCORES_undirectedsim <- (SCORES_undirectedsim + run1_a[[1]][[i]] + t(run1_a[[1]][[i]]))}
SCORES_undirectedsim <- (SCORES_undirectedsim/n)*2
AUROC_undirected_sim1 <- compute_AUROC(SCORES_undirectedsim,true_Net_undirected)
AUROC_undirected_sim

n   <- length(run2_a[[1]])
SCORES_undirectedsim <- matrix(0,11,11)
for (i in (n/2):n){
  SCORES_undirectedsim <- (SCORES_undirectedsim + run2_a[[1]][[i]] + t(run2_a[[1]][[i]]))}
SCORES_undirectedsim <- (SCORES_undirectedsim/n)*2
AUROC_undirected_sim <- compute_AUROC(SCORES_undirectedsim,true_Net_undirected)
AUROC_undirected_sim

n   <- length(run2_a[[1]])
SCORES_undirectedsim <- matrix(0,11,11)
for (i in (n/2):n){
  SCORES_undirectedsim <- (SCORES_undirectedsim + run2_a[[1]][[i]] + t(run2_a[[1]][[i]]))}
SCORES_undirectedsim <- (SCORES_undirectedsim/n)*2
AUROC_undirected_sim <- compute_AUROC(SCORES_undirectedsim,true_Net_undirected)
AUROC_undirected_sim

##### # 2.2 bayesian learning algorithms functions in bnlearn for synthetic RAF data
##2.2.1 score based algorithms for synthetic RAF data
Data.sim <- as.data.frame(t(Data.sim1))
dag.hc.bic.sim <- hc(Data.sim, score = "bic-g", start = random.graph(names(lsachs)))
dag.hc.bge.sim <- hc(Data.sim, score = "bge", start = random.graph(names(lsachs)))
dag.tabu.bic.sim <- tabu(Data.sim, score = "bic-g",start = random.graph(names(lsachs)))
dag.tabu.bge.sim <- tabu(Data.sim, score = "bge", start = random.graph(names(lsachs)))
#obtaining incidence matrix and compute AUROC 
dag.hc.bicsim.matrix <- amat(dag.hc.bic.sim)
AUROC_hcbicsim <- compute_AUROC(dag.hc.bicsim.matrix,true_Cpdag)
dag.hc.bgesim.matrix <- amat(dag.hc.bge.sim)
AUROC_hcbgesim <- compute_AUROC(dag.hc.bgesim.matrix,true_Cpdag)
dag.tabu.bicsim.matrix <- amat(dag.tabu.bic.sim)
AUROC_tabubicsim <- compute_AUROC(dag.tabu.bicsim.matrix,true_Cpdag)
dag.tabu.bgesim.matrix <- amat(dag.tabu.bge.sim)
AUROC_tabubgesim <- compute_AUROC(dag.tabu.bgesim.matrix,true_Cpdag)
AUROC_hcbicsim
AUROC_hcbgesim
AUROC_tabubicsim
AUROC_tabubgesim
#2.2.2 hybrid algorithms for synthetic RAF data
dag.mmhc.sim <- mmhc(Data.sim)
dag.rsmax.sim <- rsmax2(Data.sim, restrict = "mmpc", maximize = "hc")
dag.rsmax2.sim <- rsmax2(Data.sim, restrict = "si.hiton.pc",  maximize = "tabu")
#obtaining incidence matrix and compute AUROC 
dag.mmhc.matrixsim <- amat(dag.mmhc.sim)
AUROC_mmhcsim <- compute_AUROC(dag.mmhc.matrixsim,true_Cpdag)
dag.rsmax.matrixsim <- amat(dag.rsmax.sim)
AUROC_rsmaxsim <- compute_AUROC(dag.rsmax.matrixsim,true_Cpdag)
dag.rsmax2.matrixsim <- amat(dag.rsmax2.sim)
AUROC_rsmax2sim <- compute_AUROC(dag.rsmax2.matrixsim,true_Cpdag)
AUROC_mmhcsim
AUROC_rsmaxsim
AUROC_rsmax2sim
###2.2.3 constraint based algorithms for synthetic RAF data
##Grow-Shrink 
net1.sim <- gs(Data.sim)
net1Matrix <- amat(net1)
net1Matrix <- net1Matrix[col.order,col.order]
AUC_net1 <- compute_AUROC(net1Matrix,true_Net_undirected)
AUC_net1
##Incremental Association Markov Blanket
net2 <- iamb(Data.sim)
net2Matrix <- amat(net2)
net2Matrix <- net2Matrix[col.order,col.order]
AUC_net2 <- compute_AUROC(net2Matrix,true_Net_undirected)
AUC_net2
#Fast Incremental Association (fast.iamb):
net3 <- fast.iamb(Data.sim)
net3Matrix <- amat(net3)
net3Matrix <- net3Matrix[col.order,col.order]
AUC_net3 <- compute_AUROC(net3Matrix,true_Net_undirected)
AUC_net3
#Interleaved Incremental Association (inter.iamb):
net4 <- inter.iamb(Data.sim)
plot(net4)
net4Matrix <- amat(net4)
net4Matrix <- net4Matrix[col.order,col.order]
AUC_net4 <- compute_AUROC(net4Matrix,true_Net_undirected)
AUC_net4
#Max-Min Parents and Children (mmpc):
net5 <- mmpc(Data.sim)
plot(net5)
net5Matrix <- amat(net5)
net5Matrix <- net5Matrix[col.order,col.order]
AUC_net5 <- compute_AUROC(net5Matrix,true_Net_undirected)
AUC_net5

############################ 2.3 learning structural by averaging graphs using bootstrap
##2.3.1 for observational log transformed RAF data
# bootstrap1 averaging multiple CPDAG
start.time <- Sys.time() 
boot.log <- boot.strength(lsachs, R = 1000, algorithm = "tabu",algorithm.args = list(score = "bge",iss = 10))
boot.log[(boot.log$strength > 0.85) & (boot.log$direction >= 0.5), ]
avg.boot.log <- averaged.network(boot.log, threshold = 0.85)
end.time <- Sys.time() #the system time when the similation ends
time.taken <- end.time - start.time # The computational costs
time.taken
avg.boot.log
avg.boot.logMatrix<- amat(avg.boot.log)
avg.boot.logMatrix<-avg.boot.logMatrix[col.order,col.order]
AUROC_logboot <- compute_AUROC(avg.boot.logMatrix,true_Cpdag)
AUROC_logboot
#bootstrap2 averaging 1000 final graphs that starts from different starting graph
start.time <- Sys.time() 
nodes <- names(lsachs)
start.log <- random.graph(nodes = nodes, method = "ic-dag", num =1000, every = 20)
netlist.log <- lapply(start.log, function(net) {hc(lsachs, score = "bge", iss = 10, start = net)})
rnd.log <- custom.strength(netlist.log, nodes = nodes)
rnd.log[(rnd.log$strength > 0.85) & (rnd.log$direction >= 0.5), ]
avg.log <- averaged.network(rnd.log, threshold = 0.85)
end.time <- Sys.time() 
time.taken <- end.time - start.time # The computational costs
time.taken
avg.log
log.matrix<- amat(avg.log)
log.matrix<-log.matrix[col.order,col.order]
AUROC_log <- compute_AUROC(log.matrix,true_Net_undirected)
AUROC_log

################## 2.3.2 bootstrapping for synthezied RAF data
## bootstrap1 averaging multiple CPDAG
start.time <- Sys.time() 
boot.log <- boot.strength(Data.sim, R = 500, algorithm = "hc",algorithm.args = list(score = "bge",iss = 10))
boot.log[(boot.log$strength > 0.85) & (boot.log$direction >= 0.5), ]
avg.boot.log <- averaged.network(boot.log, threshold = 0.85)
end.time <- Sys.time() #the system time when the similation ends
time.taken <- end.time - start.time # The computational costs
time.taken
avg.boot.log
avg.boot.logMatrix<- amat(avg.boot.log)
avg.boot.logMatrix<-avg.boot.logMatrix[col.order,col.order]
AUROC_logboot <- compute_AUROC(avg.boot.logMatrix,true_Cpdag)
AUROC_logboot
#bootstrap2
start.time <- Sys.time() 
nodes <- names(Data.sim)
start.log <- random.graph(nodes = nodes, method = "ic-dag", num =1000, every = 20)
netlist.log <- lapply(start.log, function(net) {hc(Data.sim, score = "bge", iss = 10, start = net)})
rnd.log <- custom.strength(netlist.log, nodes = nodes)
rnd.log[(rnd.log$strength > 0.85) & (rnd.log$direction >= 0.5), ]
avg.log <- averaged.network(rnd.log, threshold = 0.85)
end.time <- Sys.time() 
time.taken <- end.time - start.time # The computational costs
time.taken
avg.log
log.matrix<- amat(avg.log)
log.matrix<-log.matrix[col.order,col.order]
AUROC_log <- compute_AUROC(log.matrix,true_Cpdag)
AUROC_log

######################## Part2 algorithms comparison for Marks observational continuous dataset ###################
#create the true network for marks
make_true_marks_Net <- function(){
  NETWORK <- matrix(numeric(5*5),5,5)
  #MECH
  
  #VECT
  NETWORK[2,1] <-1
  
  #ALG
  NETWORK[3,1] <-1
  NETWORK[3,2] <-1
  
  #ANL
  NETWORK[4,3] <-1
  
  #STAT
  NETWORK[5,3] <-1
  NETWORK[5,4] <-1
  return(NETWORK)
}
# generate true DAG for undirectured graph for MARKS dataset
marks_Net <- make_true_marks_Net()
marks_Cpdag <- extract_cpdag_of_dag(marks_Net) 
# generate true DAG for undirectured graph for MARKS dataset
marks_Net_undirected <- marks_Net + t(marks_Net)
### strMCMC for marks dataset
data(marks)
dim(marks)
marks.mcmc <- t(marks)
I_m <-  matrix (0,nrow =5, ncol = 5)
start.timemark <- Sys.time() # the system time when the similation starts
run.mark <- strMCMC(marks.mcmc,I_m,1000,5)
end.timemark <- Sys.time() #the system time when the similation ends
time.takenmark <- end.timemark - start.timemark # The computational costs
time.takenmark
L1_m<- (run.mark[[1]])    
L2_m<- (run.mark[[2]]) 
listm <- cpdag_list(L1_m,10)
edges_mat_m <- listm[[3]]
AUC_m <- compute_AUROC(edges_mat_m,marks_Cpdag)
AUC_m

###### algorithms implemented in bnlearn package for marks dataset
#score based algorithms dor marks data
net.hc.m1 <- hc(marks,score="bic-g",start = random.graph(names(marks)))
net.hcm.Matrix1 <- amat(net.hc.m1)
AUC_net.m.hc1 <- compute_AUROC(net.hcm.Matrix1,marks_Cpdag)
AUC_net.m.hc1
net.hc.m2 <- hc(marks,score="bge",start = random.graph(names(marks)))
net.hcm.Matrix2 <- amat(net.hc.m2)
AUC_net.m.hc2 <- compute_AUROC(net.hcm.Matrix2,marks_Cpdag)
AUC_net.m.hc2
net.tabu.m1 <- tabu(marks,score="bic-g",start = random.graph(names(marks)))
net.tabum.Matrix1 <- amat(net.tabu.m1)
AUC_net.m.tabu1 <- compute_AUROC(net.tabum.Matrix1,marks_Cpdag)
AUC_net.m.tabu1
net.tabu.m2 <- tabu(marks,score="bge",start = random.graph(names(marks)))
net.tabum.Matrix2 <- amat(net.hc.m2)
AUC_net.m.tabu2 <- compute_AUROC(net.tabum.Matrix2,marks_Cpdag)
AUC_net.m.tabu2
## hybrid algorithms for marks data
dag1 <- mmhc(marks)
dag2 <- rsmax2(marks, restrict = "mmpc", maximize = "hc")
dag3<- rsmax2(marks, restrict = "si.hiton.pc",  maximize = "tabu")
dag.Matrix1 <- amat(dag1)
dag.Matrix2 <- amat(dag2)
dag.Matrix3 <- amat(dag3)
AUC_marks1 <- compute_AUROC(dag.Matrix1,marks_Cpdag)
AUC_marks1
AUC_marks2 <- compute_AUROC(dag.Matrix2,marks_Cpdag)
AUC_marks2
AUC_marks3 <- compute_AUROC(dag.Matrix3,marks_Cpdag)
AUC_marks3
##constraint based for MARKS data
###Grow-Shrink 
net1m <- gs(marks)
net1mMatrix <- amat(net1m)
AUC_net1m <- compute_AUROC(net1mMatrix,marks_Net_undirected)
AUC_net1m
##Incremental Association Markov Blanket
net2m <- iamb(marks)
net2mMatrix <- amat(net2m)
AUC_net2m <- compute_AUROC(net2mMatrix,marks_Net_undirected)
AUC_net2m
#Fast Incremental Association (fast.iamb):
net3m <- fast.iamb(marks)
net3mMatrix <- amat(net3m)
AUC_net3m <- compute_AUROC(net3mMatrix,marks_Net_undirected)
AUC_net3m
#Interleaved Incremental Association (inter.iamb):
net4m <- inter.iamb(marks)
net4mMatrix <- amat(net4m)
AUC_net4m <- compute_AUROC(net4mMatrix,marks_Net_undirected)
AUC_net4m
#Max-Min Parents and Children (mmpc):
net5m <- mmpc(marks)
net5mMatrix <- amat(net5m)
AUC_net5m <- compute_AUROC(net5mMatrix,marks_Net_undirected)
AUC_net5m

######################################part4 #discretizated RAF observational data #########
#discretize 
dsachs <- discretize(sachs, method = "hartemink", breaks = 3, ibreaks = 60, idisc = "quantile")
##score-based
dag.hc.bde <- hc(dsachs, score = "bde",start = random.graph(names(dsachs)))
dag.hc.bde.matrix <- amat(dag.hc.bde)
dag.hc.bde.matrix <- dag.hc.bde.matrix[col.order,col.order]
AUROC_hcbde <- compute_AUROC(dag.hc.bde.matrix,true_Cpdag)
AUROC_hcbde
dag.tabu.bde <- tabu(dsachs, score = "bde",start = random.graph(names(dsachs)))
dag.tabu.bde.matrix <- amat(dag.tabu.bde)
dag.tabu.bde.matrix <- dag.tabu.bde.matrix[col.order,col.order]
AUROC_tabubde <- compute_AUROC(dag.tabu.bde.matrix,true_Cpdag)
AUROC_tabubde

##constraint based for observed discretizated RAF data
###Grow-Shrink 
net1 <- gs(dsachs)
net1Matrix <- amat(net1)
net1Matrix <- net1Matrix[col.order,col.order]
AUC_net1 <- compute_AUROC(net1Matrix,true_Net_undirected)
AUC_net1
##Incremental Association Markov Blanket
net2 <- iamb(dsachs)
net2Matrix <- amat(net2)
net2Matrix <- net2Matrix[col.order,col.order]
AUC_net2 <- compute_AUROC(net2Matrix,true_Net_undirected)
AUC_net2
#Fast Incremental Association (fast.iamb):
net3 <- fast.iamb(dsachs)
net3Matrix <- amat(net3)
net3Matrix <- net3Matrix[col.order,col.order]
AUC_net3 <- compute_AUROC(net3Matrix,true_Net_undirected)
AUC_net3
#Interleaved Incremental Association (inter.iamb):
net4 <- inter.iamb(dsachs)
net4Matrix <- amat(net4)
net4Matrix <- net4Matrix[col.order,col.order]
AUC_net4 <- compute_AUROC(net4Matrix,true_Net_undirected)
AUC_net4
#Max-Min Parents and Children (mmpc):
net5 <- mmpc(dsachs)
net5Matrix <- amat(net5)
net5Matrix <- net5Matrix[col.order,col.order]
#true_Net2 <- true_Net + t(true_Net)
AUC_net5 <- compute_AUROC(net5Matrix,true_Net_undirected)
AUC_net5
#bootstrap1
start.time <- Sys.time() 
boot.log <- boot.strength(dsachs, R = 1000, algorithm = "tabu",algorithm.args = list(score = "bde",iss = 10))
boot.log[(boot.log$strength > 0.85) & (boot.log$direction >= 0.5), ]
avg.boot.log <- averaged.network(boot.log, threshold = 0.85)
end.time <- Sys.time() #the system time when the similation ends
time.taken <- end.time - start.time # The computational costs
time.taken
avg.boot.log
avg.boot.logMatrix<- amat(avg.boot.log)
avg.boot.logMatrix<-avg.boot.logMatrix[col.order,col.order]
AUROC_logboot <- compute_AUROC(avg.boot.logMatrix,true_Cpdag)
AUROC_logboot

#bootstrap2
start.time <- Sys.time() 
nodes <- names(dsachs)
start.log <- random.graph(nodes = nodes, method = "ic-dag", num =1000, every = 20)
netlist.log <- lapply(start.log, function(net) {hc(dsachs, score = "bde", iss = 10, start = net)})
rnd.log <- custom.strength(netlist.log, nodes = nodes)
rnd.log[(rnd.log$strength > 0.85) & (rnd.log$direction >= 0.5), ]
avg.log <- averaged.network(rnd.log, threshold = 0.85)
end.time <- Sys.time() 
time.taken <- end.time - start.time # The computational costs
time.taken
avg.log
log.matrix<- amat(avg.log)
log.matrix<-log.matrix[col.order,col.order]
AUROC_log <- compute_AUROC(log.matrix,true_Cpdag)
AUROC_log


##plot
MeanAUROC<-c(0.57,0.708,0.75,0.57,0.723,0.75,0.57,0.736,0.75,0.57,0.729,0.75,0.56,0.709,1,0.675,0.765,1,0.668,0.99,1)
data_condition<- rep(c("Observed_data","Simulated_data","marks_data"),times=5)
methods<- rep(c("hc-bic","hc-bge","tabu-bic","tabu-bge","Bootstrap1","Bootstrap2","MCMC-bge"),each =3)
data_condition
sdAUROC <-  c(0,0,0,0,0,0,0,0,0,0,0,0,0,0.03,0)
data <- do.call(rbind,Map(data.frame,sdAUROC=sdAUROC,MeanAUROC = MeanAUROC, data_condition=data_condition,methods=methods))
library(ggplot2)
p <- ggplot(data, aes(fill=data_condition, y=MeanAUROC, x=methods)) 
p + geom_bar(position=position_dodge(), colour="black",stat="identity",size=.3) +
  theme_bw()+theme(axis.text.x=element_text(size=rel(2)),axis.text.y=element_text(size=rel(2)))+
  geom_errorbar(aes(ymin=MeanAUROC-sdAUROC, ymax=MeanAUROC+sdAUROC), width=.2, position=position_dodge(.9))+
  scale_fill_manual(values=c("#CCCCCC","#FFFFFF","#333333")) + coord_flip()

                                                    
###### investigating R 
setwd('')
sachs <- read.table("sachs.data.txt", header = TRUE)
sachs
length(sachs)
data("cytometryContinuous")
names("cytometryContinuous")
data
cytometryContinuous
cyto.raw <- cytometryContinuous$data
cyto.ivn <- cytometryContinuous$ivn
cyto.data <- sparsebnData(cyto.raw, type = "continuous",ivn = cyto.ivn)
print(cyto.data)
summary(cyto.data)

##MCMC
lsachs<-lsachs[,col.order]
names <- colnames(sim.data1)
colnames(lsachs) <- names
I <- matrix (0,nrow =11, ncol = 11)
start.time1a <- Sys.time() # the system time when the similation starts
run1_a <- strMCMC(lsachs,I,10000,100,3)
end.time1a <- Sys.time() #the system time when the similation ends
time.taken1a <- end.time1a - start.time1a # The computational costs
time.taken1a
L1_1a<- (run1_a[[1]])    # incidence matrix
L2_1a<- (run1_a[[2]])    # BGe



##plot
MeanAUROC<-c(0.5133,0.7634,0.9054,0.5403,0.7634,0.9054,0.5673,0.7226,0.9054,
             0.5403,0.7634,0.9054,0.5357,0.7625,0.875,0.5253,0.7295,0.749,0.73,0.78,0.92,
             0.7037,0.9078,0.9948)

sdAUROC <- rnorm(3, mean=0.04, sd=0.02) + c(0.06,0.05,0.02,0.05,0.03,0.01)
sampleSize<- rep(c("10","100","1000"),times=8)
methods<- rep(c("GS","Iamb","fastIamb","inter.iamb","mmpc","hc","greedy search","MCMC"),each =3)
sampleSize
methods
data <- do.call(rbind,Map(data.frame, sdAUROC =sdAUROC,MeanAUROC = MeanAUROC, sampleSize=sampleSize,methods=methods))
library(ggplot2)
p <- ggplot(data, aes(fill=sampleSize, y=MeanAUROC, x=methods)) 
p + geom_bar(position=position_dodge(), colour="black",stat="identity",colour="black",size=.3) +
  theme_bw()+theme(axis.text.x=element_text(size=rel(2)),axis.text.y=element_text(size=rel(2)))+
  geom_errorbar(aes(ymin=MeanAUROC-sdAUROC, ymax=MeanAUROC+sdAUROC), width=.2, position=position_dodge(.9))+
  scale_fill_manual(values=c("#CCCCCC","#FFFFFF","#333333")) + coord_flip()
                                                                                                            
      

