set.seed(2023)
library(Rlab)
library(ggplot2)
library(dplyr)
library(tidyr)


# some functions are re-written from code of the paper "Sequential Test for the Lowest Mean: From Thompson to Murphy Sampling".

delta = exp(-3)
mu <- c(0.1*(1:7))

discsolve <- function(f,xmin,xmax,delta=10^(-11))
{
  # find m such that f(m)=0 with binary search
  l=xmin
  u=xmax
  sgn = f(xmin)
  while(u-l>delta)
  {
    m=(u+l)/2
    if(f(m)*sgn>0)
    {
      l=m
    }
    else
    {
      u=m
    }
  }
  m=(u+l)/2
  return(m)
}

hinv <- function(x)
{
  if(x<1)
  {
    print("error here hey")
  }
  if(x==Inf)
  {
    return(Inf)
  }
  #fun(u) = u-log(u)-x
  fun <- function(u)
  {
    u-log(u)-x
  }
  return(discsolve(fun,x,exp(1)/(exp(1)-1)*x))
}

Theory <- function(x, sides=2)
{
  return(2*hinv(1+(hinv(1+x)+log(sides*pi^2/6))/2))
}

# compute C assuming the function minimized is convex
Cfun <- function(x)
{
  fun2 <- function(lambda)
  {
    lambda/(1-lambda) + log(1-lambda)-2*x
  }
  lambdamin=discsolve(fun2,0,1)
  return((-0.5*log(1-lambdamin)+x)/lambdamin)
}

# KL-divergence between two bernoulli distributions with mean p and q
KLBernoulli <- function(p,q)
{
  d = 0
  if(p!=q)
  {
    if(p<=0)
    {
      p=2.22*10^(-16)
    }
    if(p>=1)
    {
      p=1-2.22*10^(-16)
    }
    d = p*log(p/q)+(1-p)*log((1-p)/(1-q))
  }
  return(d)
}

# compute the theoretical sample complexity/allocation weights in the paper
theoretical_SC<- function(mu,delta,gamma)
{
  mu_min <- min(mu)
  mu_max <- max(mu)
  sum <- 0
  if(gamma>=mu_min & gamma<=mu_max)
  {
    sum <- 1/KLBernoulli(mu_min,gamma)+1/KLBernoulli(mu_max,gamma)
  }
  else
  {
    for(i in 1:length(mu))
    {
      sum <- sum + 1/KLBernoulli(mu[i],gamma)
    }
  }
  return(sum*log(1/delta))
}

theoretical_weight<- function(mu,delta,gamma)
{
  mu_min <- min(mu)
  mu_max <- max(mu)
  weight <- rep(0,length(mu))
  sum <- 0
  if(gamma>=mu_min & gamma<=mu_max)
  {
    min_index <- min(which(mu == min(mu)))
    max_index <- max(which(mu == max(mu)))
    weight[min_index] = (1/KLBernoulli(mu_min,gamma))/(1/KLBernoulli(mu_min,gamma)+1/KLBernoulli(mu_max,gamma))
    weight[max_index] = (1/KLBernoulli(mu_max,gamma))/(1/KLBernoulli(mu_min,gamma)+1/KLBernoulli(mu_max,gamma))
  }
  else
  {
    for(i in 1:length(mu))
    {
      sum <- sum + 1/KLBernoulli(mu[i],gamma)
    }
    for(j in 1:length(mu))
    {
      weight[j] <- (1/KLBernoulli(mu[j],gamma))/sum
    }
  }
  return(weight)
}

# Thompson-CHM algorithm
ThompsonCHF <- function(muhat,N,gamma,delta,K,t)
{
  indices = rep(Inf,K)
  S = muhat*N
  Ind = which(N == 0)
  if(length(Ind)>0)
  {
    tempber <- rbern(1,prob=0.5)
    if(tempber == 1)
    {
      draw <- min(which(Ind == min(Ind)))
    }
    else
    {
      draw <- max(which(Ind == max(Ind)))
    }
  }
  while(( min(indices)>gamma)|(max(indices)<gamma))
  {
    for(i in 1:K)
    {
      indices[i] = rbeta(1,S[i]+1,N[i]-S[i]+1)
    }
  }
  beta_para = (KLBernoulli(max(indices),gamma))/(KLBernoulli(max(indices),gamma)+KLBernoulli(min(indices),gamma))
  temp = rbern(1,prob=beta_para)
  if(temp == 1)
  {
    draw <- min(which(indices == min(indices)))
  }
  else
  {
    draw <- max(which(indices == max(indices)))
  }
  return(draw)
}

# stopping rules
Rejectcond1 <-function(muhat,N,gamma,delta,K,Thres=Cfun,c=2)
{
  if((min(muhat)>=gamma)&(min(N)>0))
  {
    sequ <- rep(0,K)
    for(i in 1:K)
    {
      sequ[i] = N[i]*KLBernoulli(muhat[i],gamma) - c*log(1+log(N[i]))
    }
    return(min(sequ)>Cfun(log(1/delta)))
  }
  else
  {
    return(FALSE)
  }
}

Rejectcond2 <-function(muhat,N,gamma,delta,K,Thres=Cfun,c=2)
{
  if((max(muhat)<=gamma)&(min(N)>0))
  {
    sequ <- rep(0,K)
    for(i in 1:K)
    {
      sequ[i] = N[i]*KLBernoulli(muhat[i],gamma) - c*log(1+log(N[i]))
    }
    return(min(sequ)>Cfun(log(1/delta)))
  }
  else
  {
    return(FALSE)
  }
}

Rejectcond3 <- function(muhat,N,gamma,delta,K,Thres=Cfun,c=2)
{
  V <- rep(-Inf,K^2)
  count <- 1
  for(i in 1:K)
  {
    for(j in 1:K)
    {
      if((muhat[i]<=gamma)&(muhat[j]>=gamma)&(N[i]>0)&(N[j]>0))
      {
        V[count] = min(N[i]*KLBernoulli(muhat[i],gamma)-c*log(1+log(N[i])),N[j]*KLBernoulli(muhat[j],gamma)-c*log(1+log(N[j])))
        count <- count+1
      }
    }
  }
  if(max(V)>Cfun(log(1/delta)))
  {
    return(TRUE)
  }
  else
  {
    return(FALSE)
  }
}

Stoppingrule <- function(muhat,N,gamma,delta,K,Thres=Cfun,c=2)
{
  return((Rejectcond3(muhat,N,gamma,delta,K,Cfun,2))|(Rejectcond1(muhat,N,gamma,delta,K,Cfun,2))|(Rejectcond2(muhat,N,gamma,delta,K,Cfun,2)))
}

# sample complexity
complexity <- function(mu,delta,gamma)
{
  K=length(mu)  # number of arms
  N=rep(0,K)
  S=rep(0,K)
  muhat=rep(0,K)
  finished = FALSE
  t=0
  recommondation = 1
  while(finished==FALSE)
  {
    I = ThompsonCHF(muhat,N,gamma,delta,K,t)      # select an arm using Thompson-CHF
    r = rbern(1,prob=mu[I])
    S[I] = S[I] + r
    N[I] = N[I] + 1
    muhat[I] = S[I]/N[I]
    t = t + 1
    stoptiming = Stoppingrule(muhat,N,gamma,delta,K,Cfun,2)
    finished = stoptiming
    if(t>50000)
    {
      # if after 50000 rounds the strategy has not stopped, we consider the hypothesis H0 is not rejected
      finished = TRUE
    }
  }
  if((Rejectcond1(muhat,N,gamma,delta,K,Cfun,2)==TRUE)|(Rejectcond2(muhat,N,gamma,delta,K,Cfun,2)==TRUE))
  {
    #infeasible
    recommendation = 0
  }
  return(list(t,N/t))
}

# empirical experiments setup: 7 arms with mean (0.1,0.2,0.3,0.4,0.5,0.6,0.7)

# sample complexity for different gamma's in feasible and infeasible cases
# feasible case where gamma=(0.15,0.25,0.35,0.45,0.55,0.65)
complexity_feasible = rep(0,6)
theoretical_feasible = rep(0,6)
for (i in 1:6)
{
  gamma = 0.05+0.1*i
  complexity_feasible[i] = complexity(mu,delta,gamma)[[1]]
  theoretical_feasible[i] = theoretical_SC(mu,delta,gamma)
}

# create a side-by-side layout
par(mfrow = c(1, 2))

gamma_feasible=c(0.15,0.25,0.35,0.45,0.55,0.65)
plot(gamma_feasible,complexity_feasible/log(1/delta),xaxt="none",type='b',col='blue',ylim=c(0,500),xlab="gamma",ylab="sample complexity/log(1/delta)",cex.lab=1.5)
lines(gamma_feasible,theoretical_feasible/log(1/delta),xaxt="none",type='b',col='red')
axis(1, seq(0.15,0.65,0.1))
legend('topleft',c("Thompson-CHM","theoretical lower bound"),lty=1,col=c("blue","red"),cex=1.5)


# infeasible case where gamma=(0.75,0.8,0.85,0.9,0.95)
complexity_infeasible = rep(0,5)
theoretical_infeasible = rep(0,5)
for (i in 1:5)
{
  gamma = 0.7+0.05*i
  complexity_infeasible[i] = complexity(mu,delta,gamma)[[1]]
  theoretical_infeasible[i] = theoretical_SC(mu,delta,gamma)
}
gamma_infeasible=c(0.75,0.8,0.85,0.9,0.95)
plot(gamma_infeasible,complexity_infeasible/log(1/delta),xaxt="none",type='b',col='blue',ylim=c(0,600),xlab="gamma",ylab="sample complexity/log(1/delta)",cex.lab=1.5)
lines(gamma_infeasible,theoretical_infeasible/log(1/delta),xaxt="none",type='b',col='red')
axis(1, seq(0.75,0.95,0.05))
legend('topright',c("Thompson-CHM","theoretical lower bound"),lty=1,col=c("blue","red"),cex=1.5)


# empirical proportion of samples compared to optimal allocation in feasible and infeasible cases
# feasible case when gamma= 0.25
gamma_1 = 0.25
theoretical_weight_feasible = rep(0,6)
theoretical_weight_feasible = theoretical_weight(mu,delta,gamma_1)
weight_feasible = rep(0,6)
for (i in 1:100)
{
  weight_feasible = weight_feasible + complexity(mu,delta,gamma_1)[[2]]
}
weight_feasible = weight_feasible/100

# create a side-by-side layout
par(mfrow = c(1, 2))

plot(weight_feasible,type='b',col='blue',ylim=c(0,1),xlab="arms",ylab="weight of arms",cex.lab=1.5)
lines(theoretical_weight_feasible,type='b',col='red')
legend('topright',c("Thompson-CHM","theoretical optimal allocation"),lty=1,col=c("blue","red"),cex=1.5)


# infeasible case when gamma= 0.9
gamma_2 = 0.9
theoretical_weight_infeasible = rep(0,6)
theoretical_weight_infeasible = theoretical_weight(mu,delta,gamma_2)
weight_infeasible = rep(0,6)
for (i in 1:100)
{
  weight_infeasible = weight_infeasible + complexity(mu,delta,gamma_2)[[2]]
}
weight_infeasible = weight_infeasible/100
plot(weight_infeasible,type='b',col='blue',ylim=c(0,1),xlab="arms",ylab="weight of arms",cex.lab=1.5)
lines(theoretical_weight_infeasible,type='b',col='red')
legend('topright',c("Thompson-CHM","theoretical optimal allocation"),lty=1,col=c("blue","red"),cex=1.5)


# sample complexity of Thompson-CHM scales with the confidence parameter delta
n_rep <- 100
deltas <- exp(-seq(1, 5, length.out = 6))  # delta = exp(-1), ..., exp(-5)

gamma_feas <- 0.4
gamma_infeas <- 0.9

empirical_feas <- numeric(length(deltas))
empirical_infeas <- numeric(length(deltas))
theoretical_feas <- numeric(length(deltas))
theoretical_infeas <- numeric(length(deltas))

for (i in seq_along(deltas)) {
  delta_i <- deltas[i]
  total_feas <- 0
  total_infeas <- 0
  for (j in 1:n_rep) {
    total_feas <- total_feas + complexity(mu, delta_i, gamma_feas)[[1]]
    total_infeas <- total_infeas + complexity(mu, delta_i, gamma_infeas)[[1]]
  }
  empirical_feas[i] <- total_feas / n_rep
  empirical_infeas[i] <- total_infeas / n_rep
  theoretical_feas[i] <- theoretical_SC(mu, delta_i, gamma_feas)
  theoretical_infeas[i] <- theoretical_SC(mu, delta_i, gamma_infeas)
}

# plot
par(mfrow = c(1, 2))
plot(-log(deltas), empirical_feas, type = 'b', col = 'blue', ylim=c(0,500),
     xlab = "-log(delta)", ylab = "Mean Sample Complexity")
lines(-log(deltas), theoretical_feas, type = 'b', col = 'red')
legend('topleft',c("Thompson-CHM","theoretical lower bound"),lty=1,col=c("blue","red"),cex=1.5)

plot(-log(deltas), empirical_infeas, type = 'b', col = 'blue', ylim=c(0,500),
     xlab = "-log(delta)", ylab = "Mean Sample Complexity")
lines(-log(deltas), theoretical_infeas, type = 'b', col = 'red')
legend('topleft',c("Thompson-CHM","theoretical lower bound"),lty=1,col=c("blue","red"),cex=1.5)