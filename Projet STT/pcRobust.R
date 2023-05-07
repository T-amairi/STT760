# An implementation of the PC algorithm and its robust version
# Ref : https://www.tandfonline.com/doi/abs/10.1198/106186008X381927

# import libs
library(graph) # to plot graph
library(pcalg) # only to generate data + Qn estimator + SHD

############################################################################
#                              FUNCTIONS                                   #
############################################################################
# compute the partial correlation using the recursive formula (see 2.2)
# Inputs :
# - i, j : indexes
# - k : a vector containing the given subset
# - corrMatrix : correlation matrix
computePartialCorr = function(i, j, k, corrMatrix)
{
  # cardinality of the subset k
  l = length(k)
  
  # if k is empty : compute the correlation directly
  if(l == 0)
  {
    return(corrMatrix[i,j])
  }
  
  # if k is containing one element : use formula 2.2
  else if(l == 1)
  {
    corr1 = corrMatrix[i,j]
    corr2 = corrMatrix[i,k[1]]
    corr3 = corrMatrix[k[1],j]
    
    n = corr1 - corr2 * corr3
    d = sqrt((1 - corr2^2) * (1 - corr3^2))
    
    return(n / d)
  }
  
  # otherwise, recursive calls using also formula 2.2
  p1 = computePartialCorr(i, j, k[2:l], corrMatrix)
  p2 = computePartialCorr(i, k[1], k[2:l], corrMatrix)
  p3 = computePartialCorr(k[1], j, k[2:l], corrMatrix)
  
  n = p1 - p2 * p3
  d = sqrt((1 - p2^2) * (1 - p3^2))
  
  return(n / d)
}

# first step of the PC algorithm to get the underlying skeleton from the given data
# Inputs :
  # - data : a data frame containing the data
  # - method : same parameter than the one in the computePartialCorr function
  # - alpha : the significance level for testing partial correlations
getSkeleton = function(data, method, alpha)
{
  phi = qnorm(1 - alpha/2) # inverse cdf of N(0,1)
  hasFinished = FALSE # to stop the while loop
  V = ncol(data) # number of nodes
  n = nrow(data) # number of samples
  l = -1 # fixes the size of the subset k
  
  S = lapply(seq_len(V), function(.) vector("list", V)) # separation set S
  C = matrix(1, V, V) - diag(V) # adjacency matrix of a full graph
  
  # correlation matrix based on the method. 
  # PS : "QnStable" is suggested by the paper itself
  corrMatrix = if(method == "robust") mcor(data, method = "QnStable") else cor(data)
  
  # see "Algorithm 1 The PCpop-algorithm" from the ref paper
  while(!hasFinished)
  {
    l = l + 1
    # select all pair of nodes (i,j) that are adjacent
    adjPairs = which(C == 1, arr.ind = TRUE)
    # order them
    adjPairs = adjPairs[order(adjPairs[,1]),]
    # number of adjacent pairs
    nPairs = nrow(adjPairs)
    
    # loop over all nodes i - j
    for(x in 1:nPairs)
    {
      # get nodes indexes
      i <- adjPairs[x, 1]
      j <- adjPairs[x, 2]
      
      # get |adj(C,i)|
      cardAdj = sum(C[i,])
      
      # check if |adj(C,i) \ {j}| >= l
      if(cardAdj - 1 >= l)
      {
        # get the combinations of indexes of size l
        IdxCombs = asplit(combn(cardAdj - 1,l), MARGIN = 2)
        # get the indexes that are adjacent to node i
        AllIdx = which(C[i,] == 1)
        # remove the index corresponding to the edge i - j
        AllIdx = AllIdx[which(AllIdx != j)]
          
        # loop over k combinations
        for(comb in IdxCombs)
        {
          # get the subset k in adj(C,i) \ {j} of size l
          k = AllIdx[comb]
          # compute corr(i,j | k)
          partialCorr = computePartialCorr(i,j,k,corrMatrix)
          # Fisher’s z-transform (see 2.3)
          Z = 0.5 * log((1 + partialCorr) / (1 - partialCorr))
          
          # independence test 
          if(sqrt(n - l - 3) * abs(Z) <= phi)
          {
            C[i,j] = C[j,i] = 0 # remove edge i - j
            S[[i]][[j]] = S[[j]][[i]] = k # add k to the separation S
            break
          }
        }
      }
    }
    
    hasFinished = TRUE
    
    # check if there is a pair of nodes (i,j) that is |adj(C,i) \ {j}| >= l
    # if it is not the case, we break from the loop
    for(i in 1:V)
    {
      if(sum(C[i,]) - 1 >= l)
      {
        hasFinished = FALSE
        break
      }
    }
  }
  
  # transform C to a data frame
  C = as.data.frame(C)
  colnames(C) = colnames(data)
  rownames(C) = colnames(data)
  return(list(C, S))
}

# second step of the PC algorithm to extend the skeleton to a CPDAG
# Inputs :
# - GSkel : the adjacency matrix of the skeleton
# - S : separation set
getCPDAG = function(GSkel, S)
{
  V = ncol(GSkel) # number of nodes
  PDAG = GSkel
  
  # select all pair of nodes (i,j) that are adjacent
  adjPairs = which(GSkel == 1, arr.ind = TRUE)
  # number of adjacent pairs
  nPairs = nrow(adjPairs)
  
  # see "Algorithm 2 Extending the skeleton to a CPDAG" from the ref paper
  # first step : set v-structures to form the PDAG
  for(x in 1:nPairs)
  {
    # get i - k
    i <- adjPairs[x, 1]
    k <- adjPairs[x, 2]
    
    for(j in 1:V)
    {
      if(i != j && GSkel[j,k] == 1 && GSkel[i,j] == 0)
      {
        # check separation condition
        if(!(k %in% S[[i]][[j]]))
        {
          # replace i - k - j by i -> k <- j
          PDAG[k,i] = PDAG[k,j] = 0
          PDAG[i,k] = PDAG[j,k] = 1
        }
      }
    }
  }
  
  CPDAG = PDAG
  stop = FALSE # to stop the while loop
  
  # second step : orient as many undirected edges as possible using
  # rules R1-R3 of the PC algorithm as given in Algorithm 2 of Kalisch and Bühlmann (2007)
  while(!stop)
  {
    stop = TRUE
    
    # select all pair of nodes (i,j) that are adjacent
    adjPairs = which(CPDAG == 1, arr.ind = TRUE)
    # number of adjacent pairs
    nPairs = nrow(adjPairs)
    
    for(x in 1:nPairs)
    {
      # get the adjacent pairs
      i <- adjPairs[x, 1]
      j <- adjPairs[x, 2]
      
      # check if i - j
      if(CPDAG[j,i] == 1)
      {
        for(k in 1:V)
        {
          # R1
          if(CPDAG[k,i] == 1 && CPDAG[i,k] == 0 && CPDAG[k,j] == 0 && CPDAG[j,k] == 0)
          {
            CPDAG[j,i] = 0 # i - j becomes i -> j
            stop = FALSE # and reset the loop condition to check again
          }
          
          # R2
          else if(CPDAG[i,k] == 1 && CPDAG[k,i] == 0 && CPDAG[k,j] == 1 && CPDAG[j,k] == 0)
          {
            CPDAG[j,i] = 0 # i - j becomes i -> j
            stop = FALSE # reset the loop condition to check again
          }
          
          # R3
          else if(CPDAG[i,k] == 1 && CPDAG[k,i] == 1 && CPDAG[k,j] == 1 && CPDAG[j,k] == 0)
          {
            for(l in 1:V)
            {
              if(CPDAG[k,l] == 0 && CPDAG[l,k] == 0 && CPDAG[i,l] == 1 && CPDAG[l,i] == 1 && CPDAG[l,j] == 1 && CPDAG[j,l] == 0)
              {
                CPDAG[j,i] = 0 # i - j becomes i -> j
                stop = FALSE # and reset the loop condition to check again
              }
            }
          }
        }
      }
    }
  }
  
  return(CPDAG)
}

# create graphNEL object using an adjacency data frame
# Inputs :
# - G : the adjacency data frame
getGraphNEL = function(G)
{
  return(as(as(G, "matrix"), "graphNEL"))
}

# PC algorithm
# Inputs :
# - data : a data frame containing the data
# - method : "robust" to use the Qn estimator or any string for the classic method
# - alpha : the significance level for testing partial correlations (default 0.01)
PCAlgo = function(data, method, alpha = 0.01)
{
  # get skeleton and separation set
  res = getSkeleton(data, method, alpha)
  GSkel = res[[1]]
  S = res[[2]]
  
  # return CPDAG
  return(getCPDAG(GSkel,S))
}

############################################################################
#                                  TEST                                    #
############################################################################
set.seed(0) # set seed for reproducibility
p = 10 # number of random variables
n = 1000 # number of samples
s = 0.2 # sparseness of the graph
DAG = randomDAG(p,s) # generate a random DAG

# generate Gaussian data 
gaussianData = rmvDAG(n, DAG, errDist= "normal")
# generate contaminated Gaussian data with 10 % Cauchy outliers
contaminatedGaussianData = rmvDAG(n, DAG, errDist= "mix")

# With Gaussian data
PCAlgoOG = getGraphNEL(PCAlgo(gaussianData,"OG"))
PCAlgoRobust = getGraphNEL(PCAlgo(gaussianData,"robust"))

par(mfrow=c(1,3)) # plot
plot(DAG, main = "True DAG")
plot(PCAlgoOG, main = paste("Estimated CPDAG (original)\nSHD = ",shd(PCAlgoOG,DAG)))
plot(PCAlgoRobust, main = paste("Estimated CPDAG (robust)\nSHD = ",shd(PCAlgoRobust,DAG)))

# With contaminated Gaussian data
PCAlgoOG = getGraphNEL(PCAlgo(contaminatedGaussianData,"OG"))
PCAlgoRobust = getGraphNEL(PCAlgo(contaminatedGaussianData,"robust"))

par(mfrow=c(1,3)) # plot
plot(DAG, main = "True DAG")
plot(PCAlgoOG, main = paste("Estimated CPDAG (original)\nSHD = ",shd(PCAlgoOG,DAG)))
plot(PCAlgoRobust, main = paste("Estimated CPDAG (robust)\nSHD = ",shd(PCAlgoRobust,DAG)))
