library('nloptr')
library('dplyr')
library('purrr')
library('tensorA')
library('optimx')
library('numDeriv')
library('dfoptim')
library('ggplot2')
library('lubridate')
library('gridExtra')
library("MASS")
library("survival")
library('fitdistrplus')
library('actuar')
library('gamlss')
library('matrixcalc')
library("rgenoud")
library("gafit")
library("scatterplot3d")
library("graphics")
library('Matrix')


source("~/Documentos/tesis/Scripts_R/AutoCluster4.R")


setwd("~/Documentos/tesis/Scripts_R")
dframe <- read.csv("BD-LC-SM.csv",sep=";",dec=",")
#-------------------set variables-----------------------

nobs<-1374
nalt<-9
k<-5
nvar<-5

covariates<-NULL
y<-NULL
y.dual<-NULL


v.dual<-c(-1,-0.5,0,0.5,1)/sqrt(nobs)
s.dual <- matrix(seq(from = 0, to = 1, length.out = 5), nrow = 1)

#s.dual<-c(0.2,0.4,0.6,0.8,1)

TCAM        <-dframe[1:nobs,19:(19 + (nalt - 1))]/60  #tiempo de caminata
TVIB        <-dframe[1:nobs,28:(28 + (nalt - 1))]/60  #tiempo de viaje sin desagregacion personal
TESP        <-cbind(rep(0,nobs),rep(0,nobs),dframe[1:nobs,39:(39 + (nalt - 3))])/60 #tiempo de espera
DISP        <-dframe[1:nobs,71:(71 + (nalt - 1))] #disponibilidad de medio de transporte
ILM         <-dframe[1:nobs,5] #ingreso lquido mensual
HTS         <-dframe[1:nobs,2] #horas de trabajo por semana
#CHOICE     <-dframe[1:nobs,81:(81 + (nalt-1))] #eleccion tomada por el decisor
CTOT        <-dframe[1:nobs,46:(46 + (nalt - 1))] #costo total en pesos chilenos
W           <- ILM/(4.3*HTS*60)
CTOT_W      <- CTOT/W
CONST       <-matrix(0,nrow = nobs, ncol= (nalt))
ICHOICE     <-dframe[1:nobs,6]
IDXM        <- cbind(seq(1, nobs), ICHOICE)
CHOICE      <- matrix(0,nobs,nalt)
CHOICE[IDXM] <- 1
NAUTLIC      <-cbind(dframe$AUTLIC[1:nobs],rep(0,nobs),rep(0,nobs),rep(0,nobs),
                     rep(0,nobs),dframe$AUTLIC[1:nobs],rep(0,nobs),rep(0,nobs),rep(0,nobs))

#---------------------determinar matriz de variables exogenas-----------------

pi<-array(dim = c(nobs,(nalt),length(s.dual)))

#---------------------total of covariates----------------------

cov.lambda.total<-array(dim = c(nobs, nvar ,nalt))
for(i in 1:(nalt)){
    cov.lambda.total[,,i]<-cbind(TCAM[ ,i], TESP[,i],   TVIB[,i],
                           CTOT_W[ ,i],NAUTLIC[,i])
} 


cov.beta.total<-unlist(cbind(rep(1,nobs), dframe$SEXO[1:nobs]))


#----------------------covariates lambda  minus TCAM------------------------

cov.lambda.1<-array(dim = c(nobs, (nvar -1) ,nalt))
for(i in 1:(nalt)){
  cov.lambda.1[,,i]<-cbind( TESP[,i],   TVIB[,i],
                         CTOT_W[ ,i])
}


#----------------------covariates lambda minus TESP--------------------------

cov.lambda.2<-array(dim = c(nobs, (nvar -1),nalt))
for(i in 1:(nalt)){
  cov.lambda.2[,,i]<-cbind( TCAM[,i],   TVIB[,i],
                          CTOT_W[ ,i])
} 

#----------------------covariates lambda minus TVIB--------------------------

cov.lambda.3<-array(dim = c(nobs, (nvar - 1) ,nalt))
for(i in 1:(nalt)){
  cov.lambda.3[,,i]<-cbind( TCAM[,i],   TESP[,i],
                          CTOT_W[ ,i])
} 

#----------------------covariates lambda minus CTOT_W-------------------------

cov.lambda.4<-array(dim = c(nobs, (nvar - 1) ,nalt))
for(i in 1:(nalt)){
  cov.lambda.4[,,i]<-cbind( TCAM[,i],   TESP[,i],
                          TVIB[ ,i])
} 0.01

#-------------------covariates beta minus NAUT/LTOT---------------------------

cov.beta.1<-unlist(cbind(rep(1,nobs), dframe$SEXO[1:nobs]))
for(i in 1:nobs){
  for(j in 1:2){
    if(is.nan(cov.beta.1[i,j]) | cov.beta.1[i,j] == Inf ){cov.beta.1[i,j] = 0}
  }
}

#-----------------------covariates beta minus SEX-----------------------------

cov.beta.2<-unlist(cbind(rep(1,nobs), (dframe$NAUT[1:nobs]/dframe$LTOT[1:nobs])))
for(i in 1:nobs){
  for(j in 1:2){
    if(is.nan(cov.beta.2[i,j]) | cov.beta.2[i,j] == Inf ){cov.beta.2[i,j] = 0}
  }
}



M<-matrix(0,nrow = nobs,ncol = nalt)
for(i in 1:nobs){
    for(j in 1:nalt)
      if(DISP[i,j] ==0){
        M[i,j] =1000
        
      }
}


#----------------------define initial parameter -------------------------------


initial.dual.total<-c(rep(0,nvar),rep(0,nobs),rep(0, 2*(nalt- 1)))
initial.dual.1<-c(rep(0,(nvar -1)),rep(0,nobs),rep(0, (3*(nalt - 1) -(nalt - 4) - (nalt - 3))))
initial.dual.2<-c(rep(0,(nvar)),rep(0,nobs),rep(0, (3*(nalt - 1) -(nalt - 4) - (nalt - 3))))


#--------------------------------define dual function---------------------------

dual<-function(x.obj, cov.lambda, cov.beta, nvar){
  lambda    <- x.obj[1:nvar]
  rho       <- x.obj[(nvar +1): ( nvar + nobs)]
  x1        <- ( nvar + nobs)
  beta      <- rbind(x.obj[(x1 + 1):(x1 + 8)],x.obj[(x1 + 9):(x1 + 16)] )
  beta      <- cbind(beta, rep(0,2))
  y         <- CHOICE
  

  util.lambda <-matrix(nrow = nobs, ncol = nalt) 
  
  for(i in 1:(nalt)){ util.lambda[,i]<-cov.lambda[,,i]%*%lambda }
 
  util.beta  <-cov.beta%*%beta
 
  
  obs.omega<-array(dim = c(nobs,(nalt),length(s.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(s.dual)){
        if(DISP[i,j] == 0){
          obs.omega[i,j,m] = 0}
        else{ obs.omega[i,j,m] = exp(s.dual[m]*((- util.lambda[i,j] - util.beta[i,j]*DISP[i,j] - rho[i])))}
      }
    }
  }
  omega <- apply(obs.omega, c(1,2), sum)
  
 # for(i in 1:nobs){
  #  for(j in 1:nalt){
   #   if(DISP[i,j]==0){
    #    omega.2[i,j] <- 0
     # }
    #}
  #}
 
  obs.psi<-array(dim = c(nobs,(nalt),length(v.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(v.dual)){
        if(DISP[i,j] == 0 && v.dual[m] >= 0){
          obs.psi[i,j,m] = 0}
        else if(DISP[i,j] == 0 && v.dual[m] < 0){
          obs.psi[i,j,m] = 0}
        else{ obs.psi[i,j,m] = exp(v.dual[m]*((- util.lambda[i,j] - util.beta[i,j]* DISP[i,j])))}
      }
    }
  }
  
  psi<-apply(obs.psi,c(1,2),sum)
  obs.lambda = y*util.lambda
  obs.beta   = beta * (t(cov.beta) %*% y)

  #y.dual<-matrix(y, nrow = nobs, ncol = nalt)*as.matrix(delta)

    return( sum(obs.beta) + sum(obs.lambda[DISP !=0]) + sum(log(omega[DISP !=0])) + sum(log(psi[DISP !=0])) + sum(rho) )
}


#-----------------------------define gradient-----------------------------------

grad.dual<-function(x.obj, cov.lambda, cov.beta, nvar){ 
  
  lambda    <- x.obj[1:nvar]
  rho       <- x.obj[(nvar +1): ( nvar + nobs)]
  x1        <- ( nvar + nobs)
  beta      <- rbind(x.obj[(x1 + 1):(x1 + 8)],x.obj[(x1 + 9):(x1 + 16)] )
  beta      <- cbind(beta, rep(0,2))
  y         <- CHOICE
  
  
  util.lambda <-matrix(nrow = nobs, ncol = nalt ) 
  
  for(i in 1:(nalt)){
    util.lambda[,i]<-cov.lambda[,,i]%*%lambda
  }
  
  util.beta  <- cov.beta%*%beta
  
  
  obs.omega<-array(dim = c(nobs,(nalt),length(s.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(s.dual)){
        if(DISP[i,j] == 0){
          obs.omega[i,j,m] = 0}
        else{ obs.omega[i,j,m] = exp(s.dual[m]*((- util.lambda[i,j] - util.beta[i,j]*DISP[i,j] - rho[i])))}
      }
    }
  } 
  
  omega<-apply(obs.omega,c(1,2),sum)
  
  
  pi<-array(dim = c(nobs,(nalt),length(s.dual)))
  p <-matrix(nrow = nobs, ncol = nalt)
  
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(s.dual)){
        if(DISP[i,j] ==0){
          pi[i,j,m]<-0
        }
        else{ pi[i,j,m]<-s.dual[m]*(obs.omega[i,j,m]/omega[i,j])}
      }
    }
  }
  
  #modificar el calculo de p?
  
  p<-apply(pi, c(1,2), sum)
  
  X.p<-matrix(nrow = nvar, ncol = nalt)
  for( i in 1:nalt){
    X.p[,i]<-t(cov.lambda[ , ,i])%*%p[,i]
  }
  
  
  obs.psi<-array(dim = c(nobs,(nalt),length(v.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(v.dual)){
        if(DISP[i,j] == 0  && v.dual[m] >= 0){
          obs.psi[i,j,m] = 0}
        else if(DISP[i,j] == 0 && v.dual[m] < 0){
          obs.psi[i,j,m] = 0}
        else{ obs.psi[i,j,m] = exp(v.dual[m]*((- util.lambda[i,j] - util.beta[i,j]*DISP[i,j] )))}
      }
    }
  }
  
  
  psi<-apply(obs.psi,c(1,2),sum)
  
  w<-array(dim = c(nobs,(nalt),length(v.dual)))
  error<-matrix(nrow = nobs, ncol = nalt)
  
  
  
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(s.dual)){
        if(DISP[i,j] ==0){
          w[i,j,m]<-v.dual[m]*(obs.psi[i,j,m])
        }
        else{ w[i,j,m]<-v.dual[m]*(obs.psi[i,j,m]/psi[i,j])}
      }
    }
  }
  
  error<-apply(w, c(1,2), sum)
  
  
  X.error<-matrix(nrow = nvar, ncol = nalt)
  for( i in 1:nalt){
    X.error[,i]<-t(cov.lambda[ , ,i])%*%error[,i]
  }
  
  #y.dual<-matrix(y, nrow = nobs, ncol = nalt)
  y.X<-matrix(nrow = nvar , ncol = nalt)
  for(i in 1:nalt){
    y.X[,i]<- t(cov.lambda[ , ,i])%*%y[,i]
  }
  
  
  s.pi<-apply(pi, c(1,2), sum)
  
  X.beta<- (t(cov.beta)%*%y -t(cov.beta)%*%p - t(cov.beta)%*%error )
  
  gr.dual <- as.vector(rep(0, (3*(nalt - 1) -(nalt - 4) - (nalt - 3))) + nvar + nobs)
  
  
  #gr.dual[1:(3*(nalt - 1) -(nalt - 4) - (nalt - 3))]<- c(X.beta[1,1:8], X.beta[2,2:3], X.beta[2,7], X.beta[3,1],X.beta[3,1] )
  
  gr.dual[1:nvar]<-(apply( y.X, 1, sum) - apply(X.p, 1, sum) - apply(X.error, 1, sum) )
  gr.dual[(nvar + 1):(nvar + nobs)] <- (1 - apply( s.pi, 1, sum))
  gr.dual[(x1 + 1): (x1 + 16)] <- c(X.beta[1,1:8], X.beta[2,1:8] )
  
  
  
  
  return(gr.dual)
}

#---------------optimize problem according to kind of covariate-----------------

#total of covariates 
res1_total<-optimr(par = initial.dual.total ,fn = dual, gr = grad.dual,
             cov.lambda = cov.lambda.total, cov.beta = cov.beta.total, nvar = 5,
             hessian = FALSE,lower=  -Inf, upper= Inf, method = "BFGS",
                        control = list(
                        maxit = 3000,
                        trace =6,
                        numDeriv = TRUE,
                        REPORT = TRUE
                        ))


# dual problem without TCAM      
res2<-optimr(par = initial.dual.1 ,fn = dual, gr = grad.dual,
             cov.lambda = cov.lambda.1, cov.beta = cov.beta.total, nvar = 4,
             hessian = FALSE,lower=  -Inf, upper= Inf, method = "BFGS",
             control = list(
               maxit = 3000,
               trace =6,
               numDeriv = TRUE,
               REPORT = TRUE
             ))


# dual problem without TESP 
res3<-optimr(par = initial.dual.1 ,fn = dual, gr = grad.dual,
             cov.lambda = cov.lambda.2, cov.beta = cov.beta.total, nvar = 4,
             hessian = FALSE,lower=  -Inf, upper= Inf, method = "BFGS",
             control = list(
               maxit = 3000,
               trace =6,
               numDeriv = TRUE,
               REPORT = TRUE
             ))


# dual problem without TVIB 
res4<-optimr(par = initial.dual.1 ,fn = dual, gr = grad.dual,
             cov.lambda = cov.lambda.3, cov.beta = cov.beta.total, nvar = 4,
             hessian = FALSE,lower=  -Inf, upper= Inf, method = "BFGS",
             control = list(
               maxit = 3000,
               trace =6,
               numDeriv = TRUE,
               REPORT = TRUE
             ))


# dual problem without CTOT_W  
res5<-optimr(par = initial.dual.1 ,fn = dual, gr = grad.dual,
             cov.lambda = cov.lambda.4, cov.beta = cov.beta.total, nvar = 4,
             hessian = FALSE,lower=  -Inf, upper= Inf, method = "BFGS",
             control = list(
               maxit = 3000,
               trace =6,
               numDeriv = TRUE,
               REPORT = TRUE
             ))


# dual problem without NAUT/LTOT
res6<-optimr(par = initial.dual.2 ,dual, gr = grad.dual,
             cov.lambda = cov.lambda.total, cov.beta = cov.beta.2, nvar = 4,
             hessian = FALSE,lower=  -Inf, upper= Inf, method = "BFGS",
             control = list(
               maxit = 3000,
               trace =6,
               numDeriv = TRUE,
               REPORT = TRUE
             ))

#---------------------------------analysis of gradient--------------------------

summary.1<-summary(res4, order = "list(round(value, 3), fevals)", par.select = FALSE,print.level=2)


comp.1<-cbind(grad(dual,unlist(initial.dual), method = 'complex'),grad.dual(unlist(initial.dual)))
cbind(gHgen(initial.dual,dual),grad.dual(initial.dual))
grad.num<-grad(dual,initial.dual)


check.derivatives(.x = initial.dual, func = dual, func_grad = grad.dual,
                  check_derivatives_tol = 1e-04,
                  check_derivatives_print = "all", 
                  func_grad_name = "grad_f")


#------------------marginal effect,  normalized entropy and his pvalues---------


mrg.effect<-function(x.obj){
  lambda    <- x.obj[1:nvar]
  rho       <- x.obj[(nvar +1): ( nvar + nobs)]
  x1        <- ( nvar + nobs)
  beta      <- rbind(x.obj[(x1 + 1):(x1 + 8)],x.obj[(x1 + 9):(x1 + 16)] )
  beta      <- cbind(beta, rep(0,2))
  y         <- CHOICE
  
  
  util.lambda <-matrix(nrow = nobs, ncol = nalt ) 
  for(i in 1:(nalt)){
    util.lambda[,i]<-covariates[,,i]%*%lambda
  }
  
  util.beta  <- cov.beta%*%beta
  
  
  obs.omega<-array(dim = c(nobs,(nalt),length(s.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(s.dual)){
        if(DISP[i,j] == 0){
          obs.omega[i,j,m] = exp((s.dual[m]*(- util.lambda[i,j] - util.beta[i,j]*DISP[i,j] - M[i,j])))}
        else{ obs.omega[i,j,m] = exp(s.dual[m]*((- util.lambda[i,j] - util.beta[i,j]*DISP[i,j] - rho[i])))}
      }
    }
  } 
  
  omega<-apply(obs.omega,c(1,2),sum)
  
  
  pi2.s2<-array(dim = c(nobs,(nalt),length(s.dual)))
  for(i in 1:length(s.dual)){
    pi2.s2[,,i]<-(s.dual[i]*(obs.omega[,,i]/omega))**2
  }  
  pi2.s2<-apply(pi2.s2, c(1,2), sum)
  
  
  pi.s2<-array(dim = c(nobs,(nalt),length(s.dual)))
  for(i in 1:length(s.dual)){
    pi.s2[,,i]<-((s.dual[i]**2)*(obs.omega[,,i]/omega))
  }  
  pi.s2<-apply(pi.s2, c(1,2), sum)
  
  
  marg.lambda<-array(dim = c(nobs,nalt,nvar))
  for(i in 1:nvar){
    marg.lambda[,,i]<-lambda[i]*(pi.s2 - pi2.s2)
  }
  
  marg.beta<-array(dim = c(nobs,nalt,3))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(k in 1:3){
         marg.beta[i,j,k]<-beta[k,j]*(pi.s2[i,j] - pi2.s2[i,j])
       }
    }
  }
  return(list(marg.lambda, marg.beta))
}

marg.1<-mrg.effect(sol.1)

marg.1.lambda <--marg.1[[1]]
marg.1.beta   <--marg.1[[2]]



norm.entr<-function(x.obj, cov.lambda, cov.beta,nvar){
  
  lambda    <- x.obj[1:nvar]
  rho       <- x.obj[(nvar +1): ( nvar + nobs)]
  x1        <- ( nvar + nobs)
  beta      <- rbind(x.obj[(x1 + 1):(x1 + 8)],x.obj[(x1 + 9):(x1 + 16)] )
  beta      <- cbind(beta, rep(0,2))
  y         <- CHOICE
  
  util.lambda <-matrix(nrow = nobs, ncol = nalt) 
  
  for(i in 1:(nalt)){ util.lambda[,i]<-cov.lambda[,,i]%*%lambda }
  
  util.beta  <-cov.beta%*%beta
  
  obs.omega<-array(dim = c(nobs,(nalt),length(s.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(s.dual)){
        if(DISP[i,j] == 0){
          obs.omega[i,j,m] = 0}
        else{ obs.omega[i,j,m] = exp(s.dual[m]*((- util.lambda[i,j] - util.beta[i,j]*DISP[i,j] - rho[i])))}
      }
    }
  } 
  
  omega<-apply(obs.omega,c(1,2),sum)
  
  
  pi.lnpi<-array(dim = c(nobs,(nalt),length(s.dual)))
  for(i in 1:length(s.dual)){
    pi.lnpi[,,i]<-(obs.omega[,,i]/omega)*log((obs.omega[,,i]/omega))
  } 
  pi.lnpi<-apply(pi.lnpi, c(1,2), sum)  
  pi.lnpi[is.na(pi.lnpi)]<- 0  
  
  obs.psi<-array(dim = c(nobs,(nalt),length(v.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(v.dual)){
        if(DISP[i,j] == 0  && v.dual[m] >= 0){
          obs.psi[i,j,m] = 0}
        else if(DISP[i,j] == 0 && v.dual[m] < 0){
          obs.psi[i,j,m] = 0}
        else{ obs.psi[i,j,m] = exp(v.dual[m]*((- util.lambda[i,j] - util.beta[i,j]*DISP[i,j] )))}
      }
    }
  }
  
  psi<-apply(obs.psi,c(1,2),sum)
  
  w.lnw<-array(dim = c(nobs,(nalt),length(v.dual)))
  for(i in 1:length(v.dual)){
    w.lnw[,,i]<-(obs.psi[,,i]/psi)*log((obs.psi[,,i]/psi))
  } 
  w.lnw<-apply(w.lnw, c(1,2), sum)  
  w.lnw[is.na(w.lnw)]<- 0  
  return(list(-sum(pi.lnpi)/(nobs*nalt*log(length(s.dual))) ,
           -sum(w.lnw)/(nobs*nalt*log(length(v.dual))), 
           -apply(pi.lnpi,c(1,2),sum)/log(length(s.dual)),-apply(w.lnw,c(1,2),sum)/log(length(v.dual))))
}



#norm entropy total
sol.1<-res1$par
norm.entr.1<-norm.entr(sol.1,cov.lambda.total,cov.beta.total,5)
norm.entr.1[[1]]

#norm entropy without  TCAM
sol.2<-res2$par
norm.entr.2<-norm.entr(sol.2,cov.lambda.1,cov.beta.total,3)
norm.entr.2[[1]]

#norm entropy without  TESP
sol.3<-res3$par
norm.entr.3<-norm.entr(sol.3,cov.lambda.2,cov.beta.total,3)
norm.entr.3[[1]]


#norm entropy without  TVIB
sol.4<-res4$par
norm.entr.4<-norm.entr(sol.4,cov.lambda.3,cov.beta.total,3)
norm.entr.4[[1]]


#norm entropy without  TCTOT_W
sol.5<-res5$par
norm.entr.5<-norm.entr(sol.5,cov.lambda.4,cov.beta.total,3)
norm.entr.5[[1]]



norm.entr.k<-function(x.obj, cov.lambda, cov.beta,nvar){
  
  lambda    <- x.obj[1:nvar]
  rho       <- x.obj[(nvar +1): ( nvar + nobs)]
  x1        <-(( nvar + nobs))
  beta      <- rbind(x.obj[(x1 + 1):(x1 + 8)],c(0,x.obj[(x1+ 9):(x1 + 10)],rep(0,3),x.obj[(x1+ 11)],0),
                     c(x.obj[(x1 + 12)],rep(0,4),x.obj[(x1 + 13)],rep(0,2)))
  beta      <- cbind(beta, rep(0,3))
  
  util.lambda <-matrix(nrow = nobs, ncol = nalt )
  
  for(i in 1:(nalt)){
    util.lambda[,i]<-cov.lambda[,,i]%*%lambda
  }
  
  util.beta  <- cov.beta%*%beta
  
  obs.omega<-array(0,dim = c(nobs,nalt,k,nvar))
  for(i in 1:k){
    for(j in 1:nvar){
    obs.omega[,,i,j]<-exp(s.dual[i]*(- util.lambda[,j] - util.beta[,j] - rho))
    }
  }
  omega <- apply(obs.omega, c(1,2,4), sum)  
  
  pi.lnpi<-array(dim = c(nobs,nalt,length(s.dual),nvar))
  for(i in 1:length(s.dual)){
    for(j in 1:nvar){
    pi.lnpi[,,i,j]<-(obs.omega[,,i,j]/omega[,,j])*log((obs.omega[,,i,j]/omega[,,j]))
    } 
  }
  pi.lnpi<-apply(pi.lnpi, c(1,2,4), sum)  
  pi.lnpi[is.na(pi.lnpi)]<- 0  
  
  obs.psi<-array(0,dim = c(nobs,nalt,length(v.dual),nvar))
  for(i in 1:k){
    for(j in 1:nvar){
      obs.psi[,,i,j]<-exp(v.dual[i]*(- util.lambda[,j] - util.beta[,j]))
    }
  }
  psi <- apply(obs.psi, c(1,2,4), sum)  
  
  w.lnw<-array(dim = c(nobs,nalt,length(v.dual),nvar))
  for(i in 1:length(s.dual)){
    for(j in 1:nvar){
      w.lnw[,,i,j]<-(obs.psi[,,i,j]/psi[,,j])*log((obs.psi[,,i,j]/psi[,,j]))
    } 
  }
w.lnw<-apply(w.lnw, c(1,2,4), sum)  
  w.lnw[is.na(w.lnw)]<- 0  
  
  
  return(list(-apply(pi.lnpi,3,sum)/(nobs*nalt*log(length(s.dual))) ,
              -apply(w.lnw,3,sum)/(nobs*nalt*log(length(v.dual)))))
}


#compute of normalized entropy and chisquare of problem
norm.1<-norm.entr(sol.1,cov.lambda.total, cov.beta.total,5)
z.value.p<-(2*nobs*nalt)*log(length(s.dual))*(1 - norm.1[[1]])
z.value.w<-(2*nobs*nalt)*log(length(s.dual))*(1 - norm.1[[2]])
alpha.1<-pchisq(z.value.p,9 ,lower.tail = F)
pchisq(0 ,10000 ,lower.tail = F)
#2( N × J )ln( M)[1 − S1( pi)]


#--------------define hessian dual and p values of variables--------

hess.dual<-function(x.obj, cov.lambda, cov.beta, nvar){
  ambda    <- x.obj[1:nvar]
  rho       <- x.obj[(nvar +1): ( nvar + nobs)]
  x1        <- ( nvar + nobs)
  beta      <- rbind(x.obj[(x1 + 1):(x1 + 8)],x.obj[(x1 + 9):(x1 + 16)] )
  beta      <- cbind(beta, rep(0,2))
  y         <- CHOICE
  
  util.lambda <-matrix(nrow = nobs, ncol = nalt ) 
  
  for(i in 1:(nalt)){
    util.lambda[,i]<-cov.lambda[,,i]%*%lambda
  }
  
  util.beta  <- cov.beta%*%beta
  
  
  obs.omega<-array(dim = c(nobs,(nalt),length(s.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(s.dual)){
        if(DISP[i,j] == 0){
          obs.omega[i,j,m] = 0}
        else{ obs.omega[i,j,m] = exp(s.dual[m]*((- util.lambda[i,j] - util.beta[i,j]*DISP[i,j] - rho[i])))}
      }
    }
  } 
  
  omega<-apply(obs.omega,c(1,2),sum)
  
  
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(s.dual)){
        if(DISP[i,j] ==0){
          pi[i,j,m]<-(obs.omega[i,j,m])
        }
        else{ pi[i,j,m]<-(obs.omega[i,j,m]/omega[i,j])}
      }
    }
  }
  
  
  
  
  obs.psi<-array(dim = c(nobs,(nalt),length(v.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(v.dual)){
        if(DISP[i,j] == 0  && v.dual[m] >= 0){
          obs.psi[i,j,m] = 0}
        else if(DISP[i,j] == 0 && v.dual[m] < 0){
          obs.psi[i,j,m] = 0}
        else{ obs.psi[i,j,m] = exp(v.dual[m]*((- util.lambda[i,j] - util.beta[i,j]*DISP[i,j] )))}
      }
    }
  }

  
  
  psi<-apply(obs.psi,c(1,2),sum)
  
  
  w<-array(dim = c(nobs,(nalt),length(v.dual)))
  
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(s.dual)){
        if(DISP[i,j] ==0){
          w[i,j,m]<-(obs.psi[i,j,m])
        }
        else{ w[i,j,m]<-(obs.psi[i,j,m]/psi[i,j])}
      }
    }
  }
  
  
  hh<-matrix(rep(10, (nvar + nobs + 13)*(nvar + nobs + 13)),(nvar + nobs + 13),(nvar + nobs + 13))    
  #h.arr<-array(0,dim = c(nobs,nalt,5))
  p.s2<-0
  e.s2<-0
  p<-0
  e<-0
  for(m in 1:5){p.s2<-(s.dual[m])**2*pi[,,m]+ p.s2
  e.s2<-(v.dual[m])**2*w[,,m] + e.s2
  p<-(s.dual[m])*pi[,,m] + p
  e<-(v.dual[m])*w[,,m] + e
  
  }
  
  for(i in 1:nvar){
    for(j in 1:nvar){
      for(k in 1:5){
        hh[i,j]<-sum(covariates[,j,]*covariates[,i,]*p.s2 -
                       (covariates[,j,]*covariates[,i,])*(p**2)) +
          sum(covariates[,j,]*covariates[,i,]*e.s2 -
                (covariates[,j,]*covariates[,i,])*(e**2))
      }
    }
  }
  
  p.i.s2<-0
  e.i.s2<-0
  p2.i.s2<-0
  e2.i.s2<-0
  for(m in 1:5){
    for(l in 1:nobs){
      p.i.s2<-pi[l,,m]*s.dual[m]**2 + p.i.s2
      e.i.s2<-w[l,,m]*v.dual[m]**2 + e.i.s2
      p2.i.s2<-(pi[l,,m]*s.dual[m])**2 +  p2.i.s2
      e2.i.s2<-(w[l,,m]*v.dual[m])**2 + e2.i.s2
    }
  }
  
  for(i in (nvar + 1):(nobs + nvar)){
    hh[i,1:nvar]<-sum(covariates[(i-nvar),,]*p.i.s2 -
                        covariates[(i- nvar),,]*p2.i.s2) +
      sum(covariates[(i - nvar),,]*e.i.s2 -
            covariates[(i - nvar),,]*e2.i.s2)
  }
  
  
  
  p.j.s2<-0
  p2.j.s2<-0
  for(m in 1:5){
    for(l in 1:nalt){
      p.j.s2<-pi[,l,m]*s.dual[m]**2 + p.j.s2
      p2.j.s2<-(pi[,l,m]*s.dual[m])**2 + p2.j.s2
    }
    
    
    for(i in (nvar + 1):(nobs + nvar)){
      for(j in (nvar + 1):(nobs + nvar)){
        if(i != j){
          hh[i,j]<-0
        }
        else{hh[i,j]<- sum( p.j.s2[(i-nvar)] -  p2.j.s2[j-nvar])}
      }    
    } 
  }
  
  
  
  p.i.s2<-0
  e.i.s2<-0
  p2.i.s2<-0
  e2.i.s2<-0
  
  for(m in 1:5){
    for(l in 1:nobs){
      p.i.s2<-pi[l,,m]*s.dual[m]**2 + p.i.s2
      e.i.s2<-w[l,,m]*v.dual[m]**2 + e.i.s2
      p2.i.s2<-(pi[l,,m]*s.dual[m])**2 +  p2.i.s2
      e2.i.s2<-(w[l,,m]*v.dual[m])**2 + e2.i.s2
    }
  }
  
  
  
  for(i in 1:nvar){
    for(j in (nvar + 1):(nobs + nvar)){
      hh[i,j]<-sum(covariates[(i-nvar),j,]*p.i.s2 -
                     covariates[(i- nvar),j,]*p2.i.s2) +
        sum(covariates[(i - nvar),j,]*e.i.s2 -
              covariates[(i - nvar),j,]*e2.i.s2)
    }
  }
  
  
  temp1<-array(0,dim = c(2,2,nalt))
  for (i in 1:2){
    for(l in 1:2){
      for (j in 1:nalt){
        temp1[i,l,j]<-sum(cov.beta[,i]*cov.beta[,l]*p.i.s2 - (cov.beta[,i]*cov.beta[,l]*p.i.s2)**2)
      } 
    }
  }
  
  for(i in (nvar + nobs + 1):(nvar + nobs + 13)){
    for(j in (nvar + nobs + 1):(nvar + nobs + 13)){
      for(k in 1:3){
        hh[i,j]<-sum(covariates[,j ,]*covariates[,i ,]*(s.dual[k])**2*pi[,,k] -
                       covariates[,j,]*covariates[,i,]*(s.dual[k]*pi[,,k])**2) +
          sum(covariates[,j,]*covariates[,i,]*(v.dual[k])**2*w[,,k] -
                covariates[,j,]*covariates[,i,]*(v.dual[k]*w[,,k])**2)
      }
    }
  }
  
  
  #for(i in 1:nvars){
  # for(j in 1:5){
  #  h.arr[,,j]<-covariates[,i,]*s.dual[j]*pi[,,j]
  #}
  #}
  return(hh)
} 

hess<-jacobian(grad.dual,sol.1, cov.lambda = cov.lambda.total,cov.beta = cov.beta.total,nvar = 5,'complex')
hh<-hess.dual(sol.1,cov.lambda.total,cov.beta.total,5)

#hess.inv<-ginv(-hess)
var.matrix.lambda<-ginv(hess[1:5,1:5])
diag.var.lambda<-diag(var.matrix.lambda)
sd.lambda<-sqrt(abs(diag.var.lambda))
z.lambda<-(sol.1[1:5] -0)**2/diag.var.lambda
pchisq(z.lambda,1, lower.tail = F)
pnorm(q=z.lambda, lower.tail = FALSE)


var.matrix.beta<-ginv(hess[1379:1395,1379:1395])
diag.var.beta<-diag(var.matrix.beta)
sd.beta<-sqrt(abs(diag.var.beta))
z.beta<-((sol.1[1379:1395] -0))**2/diag.var.beta
pchisq(z.beta ,1, lower.tail = F)
pnorm(q=z.beta, lower.tail = FALSE)



#---------------------mean and standard desviation of marginal effects  according to choice and covariate----------------------------------------

MEAN<-matrix(nrow = 4,ncol = 9)
SD<-matrix(nrow = 4,ncol = 9)


for(k in 1:4){
  for(j in 1:9){
    
    MEAN[k,j]<-mean(marg.1.lambda[CHOICE[,1]==1 ,j,k])
  }
}


for(k in 1:4){
  for(j in 1:9){
    
    SD[k,j]<-sd(marg.1.lambda[CHOICE[,1]==1 ,j,k])
  }
}




#--------------------------------------graphics---------------------------------

par(mfrow=c(3, 3))


#TCAM
hist(marg.1.lambda[CHOICE[,1]==1 ,1,1],main = "Alternativa auto (como chofer)",freq =TRUE ,xlab = "efecto marginal" ,col  = "light blue")
x1fit<-seq(min(marg.1.lambda[CHOICE[,1]==1 ,1,1]),max(marg.1.lambda[CHOICE[,1]==1 ,1,1]),length=40)
y1fit<-dnorm(xfit,mean=mean(marg.1.lambda[CHOICE[,1]==1 ,1,1]),sd=sd(marg.1.lambda[CHOICE[,1]==1 ,1,1]))
y1fit <- yfit*diff(h$mids[1:2])*length(x)
lines(xfit, yfit, col="blue", lwd=2)


hist(marg.1.lambda[CHOICE[,2]==1 ,2,1],main = "Alternativa auto (como pasajero)",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
x1fit<-seq(min(marg.1.lambda[CHOICE[,1]==1 ,2,1]),max(marg.1.lambda[CHOICE[,1]==1 ,2,1]),length=40)
y1fit<-dslnorm(-xfit,mean=mean(marg.1.lambda[CHOICE[,1]==1 ,2,1]),sd=sd(marg.1.lambda[CHOICE[,1]==1 ,2,1]))
y1fit <- yfit*diff(h$mids[1:2])*length(x)
lines(xfit, yfit, col="blue", lwd=2)

hist(marg.1.lambda[ CHOICE[,3]==1 ,3,1],main = "Alternativa taxi compartido",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[ CHOICE[,4]==1 ,4,1],main = "Alternativa Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x,-20,2.5), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,5]==1 ,5,1],main = "Alternativa Bus",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,6]==1,6,1],main = "Alternativa auto (como chofer) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,7]==1,7,1],main = "Alternativa auto (como pasajero) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,8]==1,8,1],main = "Alternativa taxi compartido - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,9]==1 ,9,1],main = "Alternativa auto Bus - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x,0,1), col = 2, lty = 2, lwd = 2, add = TRUE)




#TESP
hist(marg.1.lambda[CHOICE[,1]==1 ,1,2],main = "Alternativa auto (como chofer)",freq =TRUE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,2]==1 ,2,2],main = "Alternativa auto (como pasajero)",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[ CHOICE[,3]==1 ,3,2],main = "Alternativa taxi compartido",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[ CHOICE[,4]==1 ,4,2],main = "Alternativa Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x,-20,2.5), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,5]==1 ,5,2],main = "Alternativa Bus",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,6]==1,6,2],main = "Alternativa auto (como chofer) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,7]==1,7,2],main = "Alternativa auto (como pasajero) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,8]==1,8,2],main = "Alternativa taxi compartido - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,9]==1 ,9,2],main = "Alternativa auto Bus - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x,0,1), col = 2, lty = 2, lwd = 2, add = TRUE)


#TVIB
hist(marg.1.lambda[CHOICE[,1]==1 ,1,3],main = "Alternativa auto (como chofer)",freq =TRUE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,2]==1 ,2,3],main = "Alternativa auto (como pasajero)",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[ CHOICE[,3]==1 ,3,3],main = "Alternativa taxi compartido",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[ CHOICE[,4]==1 ,4,3],main = "Alternativa Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x,-20,2.5), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,5]==1 ,5,3],main = "Alternativa Bus",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,6]==1,6,3],main = "Alternativa auto (como chofer) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,7]==1,7,3],main = "Alternativa auto (como pasajero) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,8]==1,8,3],main = "Alternativa taxi compartido - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,9]==1 ,9,3],main = "Alternativa auto Bus - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x,0,1), col = 2, lty = 2, lwd = 2, add = TRUE)



#CTOT_W
hist(marg.1.lambda[CHOICE[,1]==1 ,1,4],main = "Alternativa auto (como chofer)",freq =TRUE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,2]==1 ,2,4],main = "Alternativa auto (como pasajero)",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[ CHOICE[,3]==1 ,3,4],main = "Alternativa taxi compartido",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[ CHOICE[,4]==1 ,4,4],main = "Alternativa Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x,-20,2.5), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,5]==1 ,5,4],main = "Alternativa Bus",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,6]==1,6,4],main = "Alternativa auto (como chofer) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,7]==1,7,4],main = "Alternativa auto (como pasajero) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,8]==1,8,4],main = "Alternativa taxi compartido - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x), col = 2, lty = 2, lwd = 2, add = TRUE)
hist(marg.1.lambda[CHOICE[,9]==1 ,9,4],main = "Alternativa auto Bus - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
curve(dlnorm(x,0,1), col = 2, lty = 2, lwd = 2, add = TRUE)


#histDist(marg.5[CHOICE[,4]==1 & marg.5[,4,12]>0 ,4,12], family=LOGNO, nbins=30, line.col="darkblue", line.wd=2.5)
#dist.1.1<-fitdist(marg.5[CHOICE[,1]==1 & marg.5[,1,9]>0,1,9], distr = "pareto")
#dist.1.2<-fitdist(marg.5[CHOICE[,4]==1 & marg.5[,4,9]>0,4,9], distr = "lnorm")
#dist.1.3<-fitdist(marg.5[CHOICE[,5]==1 & marg.5[,5,9]>0,5,9], distr = "lnorm")
#dist.3<-fitdist(marg.5[CHOICE[,1]==1 & marg.5[,1,9]>0,1,9], distr = "exp")
#dist.4<-fitdist(marg.5[CHOICE[,5]==1 & marg.5[,4,10]>0,5,11], distr = "llogis")
#denscomp(list(dist.1.1, dist.3), legendtext = c("logis", "exp"),plotstyle = "ggplot")
#g <- gofstat(list(dist.2, dist.3,dist.4), fitnames = c("lnorm", "gamma","unif"))



#CHOICE[CHOICE[,5]==1,5]
#ggplot(data=dframe, aes(ILM,fill= as.factor(LasCondes))) + geom_histogram(bins= 100) +facet_grid(LasCondes ~., scales = 'free')
#subset( mrg.df.9, V5 < 1e-15)

#p1<-ggplot(data= mrg.df.12, aes(V1)) + geom_histogram(bins= 15, fill = 'purple')
#p2<-ggplot(data= mrg.df.12, aes(V2)) + geom_histogram(bins= 15, fill = 'purple')
#p3<-ggplot(data= mrg.df.12, aes(V3)) + geom_histogram(bins= 15)
#p4<-ggplot(data= mrg.df.12, aes(V4)) + geom_histogram(bins= 15)
#p5<-ggplot(data= mrg.df.12, aes(V5)) + geom_histogram(bins= 15)
#p6<-ggplot(data= mrg.df.12, aes(V6)) + geom_histogram(bins= 15)
#p7<-ggplot(data= mrg.df.12, aes(V7)) + geom_histogram(bins= 15)
#p8<-ggplot(data= mrg.df.12, aes(V8)) + geom_histogram(bins= 15)
#p9<-ggplot(data= mrg.df.12, aes(V9)) + geom_histogram(bins= 15)
#grid.arrange(p1, p2,p3,p4,p5,p6,p7,p8,p9, nrow = 3,ncol =3)


p.final<-matrix(0,nrow = nobs,ncol = nalt)
for(i in nobs){
p.final[i,]<- p[i,]/p.norm[i]  
}
data.merge<-merge(df.sol,dframe)


#------------------------infometric package-------------------------------

hist(sol.1[5:(nobs-13)], main= "Alternativa auto Bus - Metro",freq =TRUE,xlab = "efecto marginal" ,col  = "purple")

distribucion <- fitdist(as.vector(util), distr = "norm")
summary(distribucion)
plot(distribucion)

histDist(util, family=NO, nbins=30, line.col="red", line.wd=1)


util<-matrix(ncol = nalt , nrow = nobs)
for(i in 1:nobs){
  for(j in 1:nalt){
    
    util[i,j]<-(- util.lambda[i,j] - util.beta[i,j]*DISP[i,j] - rho[i])
    
    
  }
}
hist(util[,7], main= "Alternativa auto Bus - Metro",freq =TRUE,xlab = "efecto marginal" ,col  = "purple")

curve(dnorm(util), col = 2, lty = 2, lwd = 2, add = TRUE)

hist(util.2[,3],main = "Alternativa auto Bus - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "purple")

hist(p.j,main = "Alternativa auto Bus - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "purple")



X2 <- runif(30)
X2 <- array(X2, c(1376, 9, 13))
gme_mixed(y.dual,covariates[,,5],X2,optim_method = "BFGS")
