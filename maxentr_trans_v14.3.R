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
library('sciplot')



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
M<-1000


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
CTO        <-dframe[1:nobs,46:(46 + (nalt - 1))] #costo total en pesos chilenos
W           <- ILM/(4.3*HTS*60)
CTO_W      <- CTO/W
CONST       <-matrix(0,nrow = nobs, ncol= (nalt -1))
ICHOICE     <-dframe[1:nobs,6]
IDXM        <- cbind(seq(1, nobs), ICHOICE)
CHOICE      <- matrix(0,nobs,nalt)
CHOICE[IDXM] <- 1
NAUTLIC      <-cbind(dframe$AUTLIC[1:nobs],rep(0,nobs),rep(0,nobs),rep(0,nobs),
                     rep(0,nobs),dframe$AUTLIC[1:nobs],rep(0,nobs),rep(0,nobs),rep(0,nobs))

CONST<-matrix(0,nrow= nobs, ncol= nalt)




#---------------------determinar matriz de variables exogenas-----------------

pi<-array(dim = c(nobs,(nalt),length(s.dual)))

#---------------------total of covariates----------------------

cov.lambda.total<-array(dim = c(nobs, nvar,(nalt)))
for(i in 1:(nalt)){
    CONST[,i] = 1
    cov.lambda.total[,,i]<-cbind(CTO_W[ ,i],  TVIB[,i],  TESP[,i], TCAM[ ,i], 
                                 NAUTLIC[,i])
    CONST[,i] = 0
}
 # cov.lambda.total[is.nan(cov.lambda.total),,]<-0

cov.beta.total<-unlist(cbind(rep(1,nobs), dframe$SEXO[1:nobs]))

#----------------------covariates lambda  minus TCAM------------------------

cov.lambda.1<-array(dim = c(nobs, (nvar -1) ,nalt))
for(i in 1:(nalt)){
  cov.lambda.1[,,i]<-cbind( TESP[,i],   TVIB[,i],
                         CTOT_W[ ,i],NAUTLIC[,i])
}


#----------------------covariates lambda minus TESP--------------------------

cov.lambda.2<-array(dim = c(nobs, (nvar -1),nalt))
for(i in 1:(nalt)){
  cov.lambda.2[,,i]<-cbind( TCAM[,i],   TVIB[,i],
                          CTOT_W[ ,i],NAUTLIC[,i])
} 

#----------------------covariates lambda minus TVIB--------------------------

cov.lambda.3<-array(dim = c(nobs, (nvar - 1) ,nalt))
for(i in 1:(nalt)){
  cov.lambda.3[,,i]<-cbind( TCAM[,i],   TESP[,i],
                          CTOT_W[ ,i],NAUTLIC[,i])
} 

#----------------------covariates lambda minus CTOT_W-------------------------

cov.lambda.4<-array(dim = c(nobs, (nvar - 1) ,nalt))
for(i in 1:(nalt)){
  cov.lambda.4[,,i]<-cbind( TCAM[,i],   TESP[,i],
                          TVIB[ ,i],NAUTLIC[,i])
} 

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


#----------------------define initial parameter -------------------------------

initial.dual.total<-c(rep(0,nalt*nvar),rep(0,nobs),rep(0, 2*(nalt- 1)))
initial.dual.1<-c(rep(0,(nvar -1)),rep(0,nobs),rep(0, (3*(nalt - 1) -(nalt - 4) - (nalt - 3))))
initial.dual.2<-c(rep(0,(nvar)),rep(0,nobs),rep(0, (3*(nalt - 1) -(nalt - 4) - (nalt - 3))))


#--------------------------------define dual-----------------------------------

dual<-function(x.obj, cov.lambda, cov.beta,nvar){
  lambda<- rep(0, nalt*nvar)
  rho       <- x.obj[((nvar)*nalt +1): ( (nvar)*nalt + nobs)]
  x1        <-(nvar*nalt   + nobs)
  beta      <- rbind(x.obj[(x1 + 1):(x1 + 8)],x.obj[(x1 + 9):(x1 + 16)] ) 
  beta      <- cbind(beta, rep(0,1))
  y         <- CHOICE
  

  
  X<-array(0,dim = c(nalt*nvar,nobs,nalt))
    for(i in 1:nobs){
      for(j in 1:nalt){
      #  cov.lambda[,j,]<- cov.lambda[,j,]*DISP
        X[((j -1 )*nvar +1):(j*nvar),i,j]<- cov.lambda[i,,j]
       lambda[((j -1 )*nvar +1):(j*nvar)]<- x.obj[((j -1)*(nvar) +1):(j*(nvar))]
       }
    }
    

       
  u.lambda <-matrix(0,nrow = nobs, ncol = nalt) 
  for(j in 1:nalt){ u.lambda[,j]<- t(X[,,j])%*%lambda*DISP[,j]}
  
  u.beta  <- cov.beta%*%beta
  

  
  obs.omega<-array(dim = c(nobs,(nalt),length(s.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(s.dual)){
      obs.omega[i,j,m] = DISP[i,j]*exp(s.dual[m]*((- u.lambda[i,j] - u.beta[i,j] - rho[i])))}
      }
    }
  
  omega <- apply(obs.omega, c(1,2), sum)*DISP + (1- DISP)
  

 
  obs.psi<-array(dim = c(nobs,(nalt),length(v.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(v.dual)){
        obs.psi[i,j,m] =DISP[i,j]*exp(v.dual[m]*( - u.lambda[i,j] - u.beta[i,j]))}
      }
    }

  psi<-apply(obs.psi,c(1,2),sum)*DISP + (1 - DISP)
  obs.lambda = y*u.lambda
  obs.beta   = beta * (t(cov.beta) %*% y)

  #y.dual<-matrix(y, nrow = nobs, ncol = nalt)*as.matrix(delta)

    return( sum(obs.beta) + sum(obs.lambda)  + sum(log(omega)) + sum(log(psi)) + sum(rho) )
}


#-----------------------------define gradient-----------------------------------

grad.dual<-function(x.obj, cov.lambda, cov.beta,nvar){
  
  lambda<- rep(0, nalt*nvar)
  rho       <- x.obj[((nvar)*nalt +1): ( (nvar)*nalt + nobs)]
  x1        <-(nvar*nalt   + nobs)
  beta      <- rbind(x.obj[(x1 + 1):(x1 + 8)],x.obj[(x1 + 9):(x1 + 16)] )
  beta      <- cbind(beta, rep(0,1))
  y         <- CHOICE
  
  
  X<-array(0,dim = c(nalt*nvar,nobs,nalt))
  for(i in 1:nobs){
    for(j in 1:nalt){
      
      #  cov.lambda[,j,]<- cov.lambda[,j,]*DISP
      X[((j -1 )*nvar +1):(j*nvar),i,j]<- cov.lambda[i,,j]
      lambda[((j -1 )*nvar +1):(j*nvar)]<- x.obj[((j -1)*(nvar) +1):(j*(nvar))]
    }
  }
  
 
  
  
  u.lambda <-matrix(0,nrow = nobs, ncol = nalt) 
  for(j in 1:nalt){ u.lambda[,j]<- t(X[,,j])%*%lambda*DISP[,j]}
  
  u.beta  <- cov.beta%*%beta
  
  
  obs.omega<-array(dim = c(nobs,(nalt),length(s.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(s.dual)){
       obs.omega[i,j,m] <- DISP[i,j]*exp(s.dual[m]*((- u.lambda[i,j] - u.beta[i,j] - rho[i])))}
      }
    }
  

  obs.psi<-array(dim = c(nobs,(nalt),length(v.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(v.dual)){
         obs.psi[i,j,m] = DISP[i,j]*exp(v.dual[m]*(- u.lambda[i,j] - u.beta[i,j]))}
      }
    }
  
  
  omega<-apply(obs.omega,c(1,2),sum)*DISP + (1 - DISP)
  psi<-apply(obs.psi,c(1,2),sum)*DISP + (1 - DISP)
  
  
  
  pi<-array(dim = c(nobs,(nalt),length(s.dual)))

  w<-array(dim = c(nobs,(nalt),length(v.dual)))

  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:5){
       pi[i,j,m]<-DISP[i,j]*s.dual[m]*(obs.omega[i,j,m]/omega[i,j])
       w[i,j,m] <-DISP[i,j]*v.dual[m]*(obs.psi[i,j,m]/psi[i,j])}
      }
    }

  
  e<-apply(w, c(1,2), sum)
  p<-apply(pi, c(1,2), sum)
  
  
  p.1<-vector(length = nobs*nalt)
  X.1<-matrix(nrow = (nalt*nvar), ncol = (nobs*nalt))
  e.1<-vector(length = nobs*nalt)
  y.1<-vector(length = nobs*nalt)
  
  for(i in 1:(nalt)){
    X.1[,((i-1)*(nobs) +1):(i*nobs)]<-X[,,i]
    
    p.1[((i-1)*(nobs) +1):(i*nobs)]<-p[,i]
    
    e.1[((i-1)*(nobs) +1):(i*nobs)]<-e[,i]
    
    y.1[((i-1)*(nobs) +1):(i*nobs)]<-y[,i]
    
  }
  
 # X.beta<- (t(cov.beta)%*%y -t(cov.beta)%*%p - t(cov.beta)%*%e )
  
  s.pi<-apply(pi, c(1,2), sum)
  
  #gr.dual <- rep(0, (nobs*(nvar +1)))
  
  gr.dual <- as.vector(rep(0, nalt*(nvar) + nobs + 16))
  
  tmp<-( X.1%*%y.1 - X.1%*%p.1 - X.1%*%e.1)
  
  X.beta<- (t(cov.beta)%*%y -t(cov.beta)%*%p - t(cov.beta)%*%e )
  
  for(i in 1:nalt){
    gr.dual[((i -1)*nvar +1):(i*nvar)]<- tmp[((i -1)*nvar +1):(i*nvar)]
  }

  gr.dual[((nvar*nalt) + 1):((nvar*nalt) + nobs)] <- (1 - apply( s.pi, 1, sum))

  gr.dual[(x1 + 1): (x1 + 16)] <- c(X.beta[1,1:8], X.beta[2,1:8] )
  
  return(gr.dual)
}

#--------------------second part of problem--------------------------------------

initial.dual.total.ind<-c(rep(0,sum(DISP)),rep(0,(nvar + 9 )))



dual.ind<-function(x.obj.ind,cov.lambda,cov.beta,nvar, x.obj){
  
  
  lambda<- rep(0, nalt*nvar)
  gamma <- matrix(0,nrow = nobs,ncol =nalt)
  
  
  #gamma <-rep(0,nalt*nobs)
  rho       <- x.obj[((nvar)*nalt +1): ( (nvar)*nalt + nobs)]
  x1        <-(nvar*nalt   + nobs)
  beta      <- rbind(x.obj[(x1 + 1):(x1 + 8)],x.obj[(x1 + 9):(x1 + 16)] )
  beta      <- cbind(beta, rep(0,1))
  y         <- CHOICE
  count     <-0
  
  
  z         <- rbind(seq(from = -0.912, to = 1.088 ,length.out = 5), seq(from = -0.8766 , to = 1.12 ,length.out = 5), seq(from = 0.06, to =  2.06,length.out = 5),
                     seq(from = -0.8479, to = 1.1521 ,length.out = 5), seq(from = -5.443, to = -7.1546 ,length.out = 5), seq(from =  -1.576, to = 2.303,length.out = 5),
                     seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10,length.out = 5),
                     seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10,length.out = 5), 
                     seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10,length.out = 5))
  
  #z         <- rbind(seq(from = 0.0762, to = 0.09979 ,length.out = 5), seq(from = 0.1075 , to = 0.1393 ,length.out = 5), seq(from = 0.921, to =  1.2,length.out = 5),
   #                  seq(from = 0.2855, to = 0.3545 ,length.out = 5), seq(from = -6.443, to = -6.1546 ,length.out = 5), seq(from =  -1.576, to = 2.303,length.out = 5),
  #                   seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10,length.out = 5),
   #                  seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10,length.out = 5), 
  
    #                   seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10,length.out = 5))
  

  phi      <- x.obj.ind[(sum(DISP) +1):(sum(DISP) + (nvar  + 9))] #falta sex y intercept en k
  phi      <- c(phi,0)
  
    X.2 <- array(dim = c(nobs, (nvar + 10),nalt))
    CONST<-matrix(0,nrow= nobs, ncol= nalt)
    
  
  X<-array(0,dim = c(nalt*nvar,nobs,nalt))
  for(i in 1:nobs){
        gamma[i, DISP[i,]==1] <- x.obj.ind[(1 + count):(count + sum(DISP[i,]))]
        count = count + sum(DISP[i,])
    for(j in 1:nalt){
      #  cov.lambda[,j,]<- cov.lambda[,j,]*DISP
      X[((j -1 )*nvar +1):(j*nvar),i,j]<- cov.lambda[i,,j]
      lambda[((j -1 )*nvar +1):(j*nvar)]<- x.obj[((j -1)*(nvar) +1):(j*(nvar))]
      
    }
  }
  
  
  for(i in 1:nalt){
    CONST[,i] = 1
    X.2[,,i]<-cbind(cov.lambda[,,i],dframe$SEXO,CONST)
    CONST[,i] = 0
  }
  
  u.beta  <- cov.beta%*%beta
  u.lambda <-matrix(0,nrow = nobs, ncol = nalt) 
  for(j in 1:nalt){ u.lambda[,j]<- (t(X[,,j])%*%lambda)*DISP[,j]}
  
  u.total <-  ( u.lambda + u.beta + rho)*as.matrix(DISP)

  sd.3<-apply(u.total, 2, sd)*3
  
  g          <- rbind(seq(from = -sd.3[1], to = sd.3[1], length.out = 5), seq(from = -sd.3[2], to = sd.3[2], length.out = 5), seq(from = -sd.3[3], to = sd.3[3], length.out = 5),
                      seq(from = -sd.3[4], to = sd.3[4], length.out = 5), seq(from = -sd.3[5], to = sd.3[5], length.out = 5), seq(from = -sd.3[6], to = sd.3[6], length.out = 5),
                      seq(from = -sd.3[7], to = sd.3[7], length.out = 5), seq(from = -sd.3[8], to = sd.3[8], length.out = 5), seq(from = -sd.3[9], to = sd.3[9], length.out = 5))
  
  
  
      obs.omega.2<-array(dim = c(nobs,(nvar + 9),5))
      
      
      #for(i in 1:nobs){
       # for(j in 1:nalt){
          
        #  if(DISP[i,j] ==0){gamma[i,j] <-0}
          
        #}
      #}

      for(k in 1:(nvar + 9)){
        for(l in 1:5){
          obs.omega.2[,k,l] = exp(z[k,l]*(- apply(X.2[,k,]*gamma,1,sum)- phi[k]/nobs))} #falta sex y intercept en k
        }
  
  
  obs.psi.2<-array(dim = c(nobs,(nalt ),5))
    for(i in 1:(nobs)){
      for(h in 1:5){
        for(j in 1:nalt)
        {
          
          obs.psi.2[i,j,h] = exp(g[j,h]*(-gamma[i,j]))*DISP[i,j]
        }
    }
  }
  
  obs.gamma = gamma*u.total
  
  
  omega.2<-apply(obs.omega.2,c(1,2),sum)
  psi.2<-apply(obs.psi.2,c(1,2),sum)# *as.matrix(DISP)# + (1-as.matrix(DISP))
  
  
   return(sum(obs.gamma) + sum(log(omega.2)) + sum(log(psi.2[DISP==1])) + sum(phi/nobs))
}




grad.dual.ind<-function(x.obj.ind,cov.lambda,cov.beta,nvar, x.obj){
  
  
  lambda<- rep(0, nalt*nvar)
  gamma <- matrix(0,nrow = nobs,ncol =nalt)
  
  
  #gamma <-rep(0,nalt*nobs)
  rho       <- x.obj[((nvar)*nalt +1): ( (nvar)*nalt + nobs)]
  x1        <-(nvar*nalt   + nobs)
  beta      <- rbind(x.obj[(x1 + 1):(x1 + 8)],x.obj[(x1 + 9):(x1 + 16)] )
  beta      <- cbind(beta, rep(0,1))
  y         <- CHOICE
  count     <-0
  z         <- rbind(seq(from = -0.912, to = 1.088 ,length.out = 5), seq(from = -0.8766 , to = 1.12 ,length.out = 5), seq(from = 0.06, to =  2.06,length.out = 5),
                     seq(from = -0.8479, to = 1.1521 ,length.out = 5), seq(from = -5.443, to = -7.1546 ,length.out = 5), seq(from =  -1.576, to = 2.303,length.out = 5),
                     seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10,length.out = 5),
                     seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10,length.out = 5), 
                     seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10,length.out = 5))
  
  #z           <- rbind(seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200,length.out = 5),
  #                    seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200,length.out = 5),
  #                   seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200,length.out = 5),
  #                    seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200,length.out = 5), 
  #                     seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200,length.out = 5))
  
  phi      <- x.obj.ind[(sum(DISP) +1):(sum(DISP) + (nvar  + 9))] #falta sex y intercept en k
  phi      <- c(phi,0)
  
  X.2 <- array(dim = c(nobs, (nvar + 10),nalt))
  CONST<-matrix(0,nrow= nobs, ncol= nalt)
  
  
  X<-array(0,dim = c(nalt*nvar,nobs,nalt))
  for(i in 1:nobs){
    gamma[i, DISP[i,]==1] <- x.obj.ind[(1 + count):(count + sum(DISP[i,]))]
    count = count + sum(DISP[i,])
    for(j in 1:nalt){
      #  cov.lambda[,j,]<- cov.lambda[,j,]*DISP
      X[((j -1 )*nvar +1):(j*nvar),i,j]<- cov.lambda[i,,j]
      lambda[((j -1 )*nvar +1):(j*nvar)]<- x.obj[((j -1)*(nvar) +1):(j*(nvar))]
      
    }
  }
  
  
  for(i in 1:nalt){
    CONST[,i] = 1
    X.2[,,i]<-cbind(cov.lambda[,,i],dframe$SEXO,CONST)
    CONST[,i] = 0
  }
  
  u.beta  <- cov.beta%*%beta
  u.lambda <-matrix(0,nrow = nobs, ncol = nalt) 
  for(j in 1:nalt){ u.lambda[,j]<- (t(X[,,j])%*%lambda)*DISP[,j]}
  
  u.total <-  ( u.lambda + u.beta + rho)*as.matrix(DISP)
  
  sd.u.3<-apply(u.total, 2, sd)*3
  
  g          <- rbind(seq(from = -sd.u.3[1], to = sd.3[1], length.out = 5), seq(from = -sd.u.3[2], to = sd.u.3[2], length.out = 5), seq(from = -sd.u.3[3], to = sd.u.3[3], length.out = 5),
                      seq(from = -sd.u.3[4], to = sd.3[4], length.out = 5), seq(from = -sd.u.3[5], to = sd.u.3[5], length.out = 5), seq(from = -sd.u.3[6], to = sd.u.3[6], length.out = 5),
                      seq(from = -sd.u.3[7], to = sd.3[7], length.out = 5), seq(from = -sd.u.3[8], to = sd.u.3[8], length.out = 5), seq(from = -sd.u.3[9], to = sd.u.3[9], length.out = 5))
  
  
  
  lambda<- matrix(lambda, nrow = nalt, ncol = nvar , byrow = T)
  lambda<-data.frame(lambda)
  
  
 
  obs.omega.2<-array(dim = c(nobs,(nvar + 9),5))
  
  
  #for(i in 1:nobs){
  # for(j in 1:nalt){
  
  #  if(DISP[i,j] ==0){gamma[i,j] <-0}
  
  #}
  #}
  
  for(k in 1:(nvar + 9)){
    for(l in 1:5){
      obs.omega.2[,k,l] = exp(z[k,l]*(- apply(X.2[,k,]*gamma,1,sum)- phi[k]/nobs))} #falta sex y intercept en k
  }
  
  
  
  obs.psi.2<-array(dim = c(nobs,(nalt),5))
  for(i in 1:(nobs)){
    for(h in 1:5){
      for(j in 1:nalt)
      {
        obs.psi.2[i,j,h] = exp(g[j,h]*(- gamma[i,j]))*DISP[i,j]
      }
    }
  }

  
  omega.2<-apply(obs.omega.2,c(1,2),sum)
  psi.2<-apply(obs.psi.2,c(1,2),sum)*as.matrix(DISP) + (1 -as.matrix(DISP))
  
  
  lambda.ind <-array(dim = c(nobs,(nvar + 9), 5))
  error.ind  <-array(dim = c(nobs,(nalt), 5))
  
  for(k in 1:14){  
    for( l in 1:5){
      lambda.ind[,k,l]  <- z[k,l]*obs.omega.2[,k,l]/omega.2[,k]
    }
  }
  
  for(j in 1:9){
    for(h in 1:5){
      error.ind[,j,h]  <- g[j,h]*obs.psi.2[,j,h]/psi.2[,j]
    }
  }
  
  lambda.ind <- apply(lambda.ind,c(1,2),sum)
  lambda.ind <-cbind(lambda.ind,rep(0,nobs))
  
  error.ind  <- apply(error.ind,c(1,2),sum)
  
  X.z.p<-array(dim = c(nobs,(nvar + 10),nalt))
  #W.u <-matrix(nrow = nobs,ncol = nvar)
  
  for(j in 1:nalt){
    X.z.p[,,j] <- X.2[,,j]*lambda.ind
  }
  
  X.z.p<-apply(X.z.p,c(1,3),sum)
  
  tmp2<- u.total-X.z.p-error.ind
  
  rest1<-rep(0,sum(DISP))
  count2<-0
  
  for (i in 1:nobs) {
    rest1[(1 + count2):(count2 +sum(DISP[i,]))] <- tmp2[i,DISP[i,]==1]
    count2<- count2 + sum(DISP[i,])
    
  }
  
  #lambda<- matrix(lambda, nrow = nalt, ncol = nvar , byrow = T)
  #lambda<-data.frame(lambda)
  mean.lambda<- c(vapply(cbind(lambda,beta[2,1:9]), function(x) mean(x[x!=0]), numeric(1)),beta[1,1:9]) - apply(lambda.ind,2,mean)
  
  #append(as.vector(u.total- apply(X.z.p,c(1,3),sum)- apply(error.ind,1,sum))
  
  return(append(rest1, as.vector(mean.lambda[1:14])))
  
}



#---------------optimize problem according to kind of covariate-----------------

#total of covariates 
res1<-optimr(par = initial.dual.total ,fn = dual, gr = grad.dual,
             cov.lambda = cov.lambda.total , cov.beta = cov.beta.total,nvar = 5,
             hessian = FALSE,lower= -Inf, upper= Inf, method = "BFGS",
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





#--------------------------optimize second part of problem---------------------

#total of covariates, part 2 of problem
res1.ind<-optimr(par = initial.dual.total.ind ,fn = dual.ind, gr = grad.dual.ind,
                 cov.lambda = cov.lambda.total , cov.beta = cov.beta.total,nvar = 5,
                 x.obj = res1$par,
                 hessian = FALSE,lower= -Inf, upper= Inf, method = "BFGS",
                 control = list(
                   maxit = 200,
                   trace =6,
                   numDeriv = F,
                   REPORT = TRUE
                 ))


par.ind<-function(x.obj.ind,cov.lambda,cov.beta,nvar, x.obj){
  
  
  lambda<- rep(0, nalt*nvar)
  gamma <- matrix(0,nrow = nobs,ncol =nalt)
  
  
  #gamma <-rep(0,nalt*nobs)
  rho       <- x.obj[((nvar)*nalt +1): ( (nvar)*nalt + nobs)]
  x1        <-(nvar*nalt   + nobs)
  beta      <- rbind(x.obj[(x1 + 1):(x1 + 8)],x.obj[(x1 + 9):(x1 + 16)] )
  beta      <- cbind(beta, rep(0,1))
  y         <- CHOICE
  count     <-0
  z         <- rbind(seq(from = -0.912, to = 1.088 ,length.out = 5), seq(from = -0.8766 , to = 1.12 ,length.out = 5), seq(from = 0.06, to =  2.06,length.out = 5),
                     seq(from = -0.8479, to = 1.1521 ,length.out = 5), seq(from = -5.443, to = -7.1546 ,length.out = 5), seq(from =  -1.576, to = 2.303,length.out = 5),
                     seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10,length.out = 5),
                     seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10,length.out = 5), 
                     seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10 ,length.out = 5), seq(from = -10, to = 10,length.out = 5))
  
  #z           <- rbind(seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200,length.out = 5),
  #                    seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200,length.out = 5),
  #                   seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200,length.out = 5),
  #                    seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200,length.out = 5), 
  #                     seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200 ,length.out = 5), seq(from = -200, to = 200,length.out = 5))
  
  phi      <- x.obj.ind[(sum(DISP) +1):(sum(DISP) + (nvar  + 9))] #falta sex y intercept en k
  phi      <- c(phi,0)
  
  X.2 <- array(dim = c(nobs, (nvar + 10),nalt))
  CONST<-matrix(0,nrow= nobs, ncol= nalt)
  
  
  X<-array(0,dim = c(nalt*nvar,nobs,nalt))
  for(i in 1:nobs){
    gamma[i, DISP[i,]==1] <- x.obj.ind[(1 + count):(count + sum(DISP[i,]))]
    count = count + sum(DISP[i,])
    for(j in 1:nalt){
      #  cov.lambda[,j,]<- cov.lambda[,j,]*DISP
      X[((j -1 )*nvar +1):(j*nvar),i,j]<- cov.lambda[i,,j]
      lambda[((j -1 )*nvar +1):(j*nvar)]<- x.obj[((j -1)*(nvar) +1):(j*(nvar))]
      
    }
  }
  
  
  for(i in 1:nalt){
    CONST[,i] = 1
    X.2[,,i]<-cbind(cov.lambda[,,i],dframe$SEXO,CONST)
    CONST[,i] = 0
  }
  
  u.beta  <- cov.beta%*%beta
  u.lambda <-matrix(0,nrow = nobs, ncol = nalt) 
  for(j in 1:nalt){ u.lambda[,j]<- (t(X[,,j])%*%lambda)*DISP[,j]}
  
  u.total <-  ( u.lambda + u.beta + rho)*as.matrix(DISP)
  
  sd.3<-apply(u.total, 2, sd)*3
  
  g          <- rbind(seq(from = -sd.3[1], to = sd.3[1], length.out = 5), seq(from = -sd.3[2], to = sd.3[2], length.out = 5), seq(from = -sd.3[3], to = sd.3[3], length.out = 5),
                      seq(from = -sd.3[4], to = sd.3[4], length.out = 5), seq(from = -sd.3[5], to = sd.3[5], length.out = 5), seq(from = -sd.3[6], to = sd.3[6], length.out = 5),
                      seq(from = -sd.3[7], to = sd.3[7], length.out = 5), seq(from = -sd.3[8], to = sd.3[8], length.out = 5), seq(from = -sd.3[9], to = sd.3[9], length.out = 5))
  
  
  
  obs.omega.2<-array(dim = c(nobs,(nvar + 9),5))
  
  
  #for(i in 1:nobs){
  # for(j in 1:nalt){
  
  #  if(DISP[i,j] ==0){gamma[i,j] <-0}
  
  #}
  #}
  
  for(k in 1:(nvar + 9)){
    for(l in 1:5){
      obs.omega.2[,k,l] = exp(z[k,l]*(- apply(X.2[,k,]*gamma,1,sum)- phi[k]/nobs))} #falta sex y intercept en k
  }
  
  
  obs.psi.2<-array(dim = c(nobs,(nalt ),5))
  for(i in 1:(nobs)){
    for(h in 1:5){
      for(j in 1:nalt)
      {
        
        obs.psi.2[i,j,h] = exp(g[j,h]*(-gamma[i,j]))*DISP[i,j]
      }
    }
  }
  
  obs.gamma = gamma*u.total
  
  
  omega.2<-apply(obs.omega.2,c(1,2),sum)
  psi.2<-apply(obs.psi.2,c(1,2),sum)*as.matrix(DISP) + (1 -as.matrix(DISP))
  
  
  
  z.p <-array(dim = c(nobs,(nvar + 9), 5))
  g.w  <-array(dim = c(nobs,(nalt), 5))
  p          <- array(dim = c(nobs,(nvar + 9), 5))
  w          <- array(dim = c(nobs,(nalt), 5))
  
  for( l in 1:5){
    p[,,l]  <- obs.omega.2[,,l]/omega.2
  }
  
  for(h in 1:5){
    w[,,h]  <- obs.psi.2[,,h]/psi.2
  }
  
  for(k in 1:14){
    for( l in 1:5){
      z.p[,k,l]  <- z[k,l]*p[,k,l]
    }
  }
  
  for(j in 1:9){
    for(h in 1:5){
      g.w[,j,h]  <- g[j,h]*w[,j,h]
    }
  }
  
  
  lambda.ind <- apply(z.p,c(1,2),sum) 
  lambda.ind <-cbind(lambda.ind,rep(0,nobs))
 # p < - cbind(p, rep(0,nobs))
  
  error.ind  <- apply(g.w,c(1,2),sum)
  
  
  return(list(lambda.ind,error.ind,p,w,obs.omega.2,u.total,gamma, X.2,phi))
  
}

result.ind<-par.ind(res1.ind$par,cov.lambda.total,cov.beta.total,nvar,res1$par)

lambda.ind<-result.ind[[1]]
error.ind<-result.ind[[2]]
p <-result.ind[[3]]
w <-result.ind[[4]]
obs.omega.res <-result.ind[[5]]
u<-result.ind[[6]]
gamma<-result.ind[[7]]
xx<-result.ind[[8]]
phi.res<- result.ind[[9]]

summary(lambda.ind)
lambda.mean.total<-apply(lambda.ind,2,mean)
lambda.sd.total<-apply(lambda.ind,2, sd)


#-----------------------------percentage of parameters minus than zero per variable---------------

perc.ctot_w <-length(lambda.ind[lambda.ind[,1]>0,1])/length(lambda.ind[,1])
perc.tivb   <-length(lambda.ind[lambda.ind[,2]>0,2])/length(lambda.ind[,2])
perc.tesp   <-length(lambda.ind[lambda.ind[,3]>0,3])/length(lambda.ind[,3])
perc.tcam   <-length(lambda.ind[lambda.ind[,4]>0,4])/length(lambda.ind[,4])


#---------------------------------analysis of gradient--------------------------

Z<-matrix(ncol = (nvar),nrow = nalt)
for(i in 1:nalt){
  Z[i,]<-res1$par[((i -1)*(nvar) +1):(i*(nvar))]
}




summary.1<-summary(res4, order = "list(round(value, 3), fevals)", par.select = FALSE,print.level=2)


comp.1<-cbind(grad(dual,res1_ind$par, cov.lambda = cov.lambda.total,nvar =15,method = 'complex'),grad.dual(unlist(res1_ind$par,cov.lambda.total,15)))
cbind(gHgen(initial.dual,dual),grad.dual(initial.dual))
grad.num<-grad(dual,initial.dual)


check.derivatives(.x = initial.dual, func = dual, func_grad = grad.dual,
                  check_derivatives_tol = 1e-04,
                  check_derivatives_print = "all", 
                  func_grad_name = "grad_f")


#------------------marginal effect,  normalized entropy and his pvalues---------


mrg.effect<-function(x.obj, cov.lambda, cov.beta,nvar){
  
  lambda<- rep(0, nalt*nvar)
  rho       <- x.obj[((nvar)*nalt +1): ( (nvar)*nalt + nobs)]
  x1        <-(nvar*nalt   + nobs)
  beta      <- rbind(x.obj[(x1 + 1):(x1 + 8)],x.obj[(x1 + 9):(x1 + 16)] )
  beta      <- cbind(beta, rep(0,2))
  y         <- CHOICE
  
  
  X<-array(0,dim = c(nalt*nvar,nobs,nalt))
  for(i in 1:nobs){
    for(j in 1:nalt){
      #  cov.lambda[,j,]<- cov.lambda[,j,]*DISP
      X[((j -1 )*nvar +1):(j*nvar),i,j]<- cov.lambda[i,,j]
      lambda[((j -1 )*nvar +1):(j*nvar)]<- x.obj[((j -1)*(nvar) +1):(j*(nvar))]
    }
  }
  
  
  u.lambda <-matrix(0,nrow = nobs, ncol = nalt) 
  for(j in 1:nalt){ u.lambda[,j]<- t(X[,,j])%*%lambda*DISP[,j]}
  
  u.beta  <- cov.beta%*%beta
  
  
  obs.omega<-array(dim = c(nobs,(nalt),length(s.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(s.dual)){
        obs.omega[i,j,m] <- DISP[i,j]*exp(s.dual[m]*((- u.lambda[i,j]  - u.beta[i,j] - rho[i])))}
    }
  }
  
  
  omega<-apply(obs.omega,c(1,2),sum)*DISP + (1 - DISP)

  
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:5){
        pi[i,j,m]<-DISP[i,j]*s.dual[m]*(obs.omega[i,j,m]/omega[i,j])}
    }
  }
  
  lambda<-matrix(lambda,nalt,nvar,byrow = T)
  
  dpi.dx.lambda <- array(0, c(nobs, nalt, length(s.dual), nvar))
  for (i in 1:nobs) {
    for (j in 1:nalt) {
      for (m in 1:length(s.dual)) {
        for (k in 1:nvar) {
          dpi.dx.lambda[i, j, m, k] <- pi[i, j, m] * lambda[j,k] * (s[m] - sum(s * pi[i, j, ]))
        }
      }
    }
  }
  
  
  marg.lambda <- array(0, c(nobs, nalt, nvar))
  for (i in 1:nobs) {
    for (j in 1:nalt) {
      for (k in 1:nvar) {
        marg.lambda[i, j, k] <- sum(s * dpi.dx.lambda[i, j, , k])
      }
    }
  }
  marg.lambda[is.na(marg.lambda)]<-0

  return(marg.lambda)
}

marg.1.lambda<-mrg.effect(res1$par,cov.lambda.total,cov.beta.total,5)


norm.entr<-function(x.obj, cov.lambda, cov.beta,nvar){
  
  lambda<- rep(0, nalt*nvar)
  rho       <- x.obj[((nvar)*nalt +1): ( (nvar)*nalt + nobs)]
  x1        <-(nvar*nalt   + nobs)
  beta      <- rbind(x.obj[(x1 + 1):(x1 + 8)],x.obj[(x1 + 9):(x1 + 16)] )
  beta      <- cbind(beta, rep(0,2))
  y         <- CHOICE
  
  
  X<-array(0,dim = c(nalt*nvar,nobs,nalt))
  for(i in 1:nobs){
    for(j in 1:nalt){
      #  cov.lambda[,j,]<- cov.lambda[,j,]*DISP
      X[((j -1 )*nvar +1):(j*nvar),i,j]<- cov.lambda[i,,j]
      lambda[((j -1 )*nvar +1):(j*nvar)]<- x.obj[((j -1)*(nvar) +1):(j*(nvar))]
    }
  }
  
  
  u.lambda <-matrix(nrow = nobs, ncol = nalt ) 
  
  u.lambda <-matrix(0,nrow = nobs, ncol = nalt) 
  for(j in 1:nalt){ u.lambda[,j]<- t(X[,,j])%*%lambda*DISP[,j]}
  
  u.beta  <- cov.beta%*%beta
  
  obs.omega<-array(dim = c(nobs,(nalt),length(s.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(s.dual)){
        if(DISP[i,j] == 0){
          obs.omega[i,j,m] = 0}
        else{ obs.omega[i,j,m] = exp(s.dual[m]*((- u.lambda[i,j] - u.beta[i,j]*DISP[i,j] - rho[i])))}
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
        if(DISP[i,j] == 0){ obs.psi[i,j,m] = 0}
        else{ obs.psi[i,j,m] = exp(v.dual[m]*((- u.lambda[i,j] - u.beta[i,j]*DISP[i,j] )))}
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
pchisq(0 ,1 ,lower.tail = F)
#2( N × J )ln( M)[1 − S1( pi)]


#--------------define hessian dual and p values of variables--------

hess.dual<-function(x.obj, cov.lambda, cov.beta, nvar){
  lambda<- rep(0, nalt*nvar)
  rho       <- x.obj[((nvar)*nalt +1): ( (nvar)*nalt + nobs)]
  x1        <-(nvar*nalt   + nobs)
  beta      <- rbind(x.obj[(x1 + 1):(x1 + 8)],x.obj[(x1 + 9):(x1 + 16)] ) 
  beta      <- cbind(beta, rep(0,1))
  y         <- CHOICE
  
  X<-array(0,dim = c(nalt*nvar,nobs,nalt))
  for(i in 1:nobs){
    for(j in 1:nalt){
      #  cov.lambda[,j,]<- cov.lambda[,j,]*DISP
      X[((j -1 )*nvar +1):(j*nvar),i,j]<- cov.lambda[i,,j]
      lambda[((j -1 )*nvar +1):(j*nvar)]<- x.obj[((j -1)*(nvar) +1):(j*(nvar))]
    }
  }
  
  
  
  u.lambda <-matrix(0,nrow = nobs, ncol = nalt) 
  for(j in 1:nalt){ u.lambda[,j]<- t(X[,,j])%*%lambda*DISP[,j]}
  
  u.beta  <- cov.beta%*%beta
  
  
  
  obs.omega<-array(dim = c(nobs,(nalt),length(s.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(s.dual)){
        obs.omega[i,j,m] = DISP[i,j]*exp(s.dual[m]*((- u.lambda[i,j] - u.beta[i,j] - rho[i])))}
    }
  }
  
  omega <- apply(obs.omega, c(1,2), sum)*DISP + (1- DISP)
  
  
  
  
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(s.dual)){
        if(DISP[i,j] ==0){
          pi[i,j,m]<-(obs.omega.2[i,j,m])
        }
        else{ pi[i,j,m]<-(obs.omega[i,j,m]/omega[i,j])}
      }
    }
  }
  
  
  
  
  obs.psi<-array(dim = c(nobs,(nalt),length(v.dual)))
  for(i in 1:nobs){
    for(j in 1:nalt){
      for(m in 1:length(v.dual)){
        obs.psi[i,j,m] =DISP[i,j]*exp(v.dual[m]*( - u.lambda[i,j] - u.beta[i,j]))}
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
var.matrix.lambda<-ginv(hess[1:45,1:45])
diag.var.lambda<-diag(var.matrix.lambda)
sd.lambda<-sqrt(abs(diag.var.lambda))
z.lambda<-(sol.1[1:45] -0)**2/diag.var.lambda
chisq<-pchisq(z.lambda,9, lower.tail = F)
pnorm(q=z.lambda, lower.tail = FALSE)


var.matrix.beta<-ginv(hess[1379:1391,1379:1391])
diag.var.beta<-diag(var.matrix.beta)
sd.beta<-sqrt(abs(diag.var.beta))
z.beta<-((sol.1[1362:1374] -0))**2/diag.var.beta
pchisq(z.beta ,1, lower.tail = F)
pnorm(q=z.beta, lower.tail = FALSE)



#---------------------mean and standard desviation of marginal effects  according to choice and covariate----------------------------------------

MEAN<-matrix(nrow = 5,ncol = 9)
SD<-matrix(nrow = 5,ncol = 9)


for(k in 1:5){
  for(j in 1:9){
    
    MEAN[k,j]<-mean(marg.1.lambda[CHOICE[,1]==1 ,j,k])
  }
}


for(k in 1:5){
  for(j in 1:9){
    
    SD[k,j]<-sd(marg.1.lambda[CHOICE[,1]==1 ,j,k])
  }
}




#--------------------------------------graphics---------------------------------

par(mfrow=c(3, 3))


#CTOT_W

BW  <- bw.nrd(marg.1.lambda[ CHOICE[,1]==1 ,1,1])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,1]==1 ,1,1],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,1]==1 ,1,1],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,1]==1 ,1,1], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,1]==1 ,1,1],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como chofer)",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(marg.1.lambda[ CHOICE[,2]==1 ,2,1])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,2]==1 ,2,1],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,2]==1 ,2,1],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,2]==1 ,2,1], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,2]==1 ,2,1],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como pasajero)",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(marg.1.lambda[ CHOICE[,3]==1 ,3,1])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,3]==1 ,3,1],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,3]==1 ,3,1],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,3]==1 ,3,1], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,3]==1 ,3,1],xlim=lim_x,ylim=lim_y,main = "Alternativa taxi compartido",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(marg.1.lambda[ CHOICE[,4]==1 ,4,1])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,4]==1 ,4,1],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,4]==1 ,4,1],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,4]==1 ,4,1], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,4]==1 ,4,1],xlim=lim_x,ylim=lim_y,main = "Alternativa Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(marg.1.lambda[ CHOICE[,5]==1 ,5,1])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,5]==1 ,5,1],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,5]==1 ,5,1],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,5]==1 ,5,1], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,5]==1 ,5,1],xlim=lim_x,ylim=lim_y,main = "Alternativa Bus",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(marg.1.lambda[ CHOICE[,6]==1 ,6,1])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,6]==1 ,6,1],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,6]==1 ,6,1],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,6]==1 ,6,1], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,6]==1 ,6,1],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como chofer) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(marg.1.lambda[ CHOICE[,7]==1 ,7,1])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,7]==1 ,7,1],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,7]==1 ,7,1],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,7]==1 ,7,1], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,7]==1 ,7,1],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como pasajero) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(marg.1.lambda[ CHOICE[,8]==1 ,8,1])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,8]==1 ,8,1],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,8]==1 ,8,1],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,8]==1 ,8,1], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,8]==1 ,8,1],xlim=lim_x,ylim=lim_y,main = "Alternativa taxi compartido - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(marg.1.lambda[ CHOICE[,9]==1 ,9,1])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,9]==1 ,9,1],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,9]==1 ,9,1],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,9]==1 ,9,1], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,9]==1 ,9,1],xlim=lim_x,ylim=lim_y,main = "Alternativa auto Bus - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')




#TIVB
BW  <- bw.nrd(marg.1.lambda[ CHOICE[,1]==1 ,1,2])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,1]==1 ,1,2],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,1]==1 ,1,2],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,1]==1 ,1,2], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,1]==1 ,1,2],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como chofer)",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(marg.1.lambda[ CHOICE[,2]==1 ,2,2])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,2]==1 ,2,2],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,2]==1 ,2,2],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,2]==1 ,2,2], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,2]==1 ,2,2],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como pasajero)",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(marg.1.lambda[ CHOICE[,3]==1 ,3,2])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,3]==1 ,3,2],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,3]==1 ,3,2],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,3]==1 ,3,2], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,3]==1 ,3,2],xlim=lim_x,ylim=lim_y,main = "Alternativa taxi compartido",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(marg.1.lambda[ CHOICE[,4]==1 ,4,2])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,4]==1 ,4,2],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,4]==1 ,4,2],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,4]==1 ,4,2], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,4]==1 ,4,2],xlim=lim_x,ylim=lim_y,main = "Alternativa Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(marg.1.lambda[ CHOICE[,5]==1 ,5,2])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,5]==1 ,5,2],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,5]==1 ,5,2],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,5]==1 ,5,2], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,5]==1 ,5,2],xlim=lim_x,ylim=lim_y,main = "Alternativa Bus",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(marg.1.lambda[ CHOICE[,6]==1 ,6,2])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,6]==1 ,6,2],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,6]==1 ,6,2],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,6]==1 ,6,2], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,6]==1 ,6,2],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como chofer) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(marg.1.lambda[ CHOICE[,7]==1 ,7,2])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,7]==1 ,7,2],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,7]==1 ,7,2],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,7]==1 ,7,2], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,7]==1 ,7,2],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como pasajero) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(marg.1.lambda[ CHOICE[,8]==1 ,8,2])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,8]==1 ,8,2],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,8]==1 ,8,2],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,8]==1 ,8,2], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,8]==1 ,8,2],xlim=lim_x,ylim=lim_y,main = "Alternativa taxi compartido - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(marg.1.lambda[ CHOICE[,9]==1 ,9,2])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,9]==1 ,9,2],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,9]==1 ,9,2],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,9]==1 ,9,2], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,9]==1 ,9,2],xlim=lim_x,ylim=lim_y,main = "Alternativa auto Bus - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')






#TESP
BW  <- bw.nrd(marg.1.lambda[ CHOICE[,1]==1 ,1,3])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,1]==1 ,1,3],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,1]==1 ,1,3],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,1]==1 ,1,3], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,1]==1 ,1,3],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como chofer)",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(marg.1.lambda[ CHOICE[,2]==1 ,2,3])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,2]==1 ,2,3],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,2]==1 ,2,3],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,2]==1 ,2,3], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,2]==1 ,2,3],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como pasajero)",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(marg.1.lambda[ CHOICE[,3]==1 ,3,3])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,3]==1 ,3,3],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,3]==1 ,3,3],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,3]==1 ,3,3], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,3]==1 ,3,3],xlim=lim_x,ylim=lim_y,main = "Alternativa taxi compartido",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(marg.1.lambda[ CHOICE[,4]==1 ,4,3])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,4]==1 ,4,3],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,4]==1 ,4,3],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,4]==1 ,4,3], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,4]==1 ,4,3],xlim=lim_x,ylim=lim_y,main = "Alternativa Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(marg.1.lambda[ CHOICE[,5]==1 ,5,3])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,5]==1 ,5,3],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,5]==1 ,5,3],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,5]==1 ,5,3], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,5]==1 ,5,3],xlim=lim_x,ylim=lim_y,main = "Alternativa Bus",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(marg.1.lambda[ CHOICE[,6]==1 ,6,3])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,6]==1 ,6,3],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,6]==1 ,6,3],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,6]==1 ,6,3], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,6]==1 ,6,3],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como chofer) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(marg.1.lambda[ CHOICE[,7]==1 ,7,3])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,7]==1 ,7,3],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,7]==1 ,7,3],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,7]==1 ,7,3], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,7]==1 ,7,3],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como pasajero) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(marg.1.lambda[ CHOICE[,8]==1 ,8,3])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,8]==1 ,8,3],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,8]==1 ,8,3],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,8]==1 ,8,3], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,8]==1 ,8,3],xlim=lim_x,ylim=lim_y,main = "Alternativa taxi compartido - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(marg.1.lambda[ CHOICE[,9]==1 ,9,3])
grilla.beta             <- density(marg.1.lambda[ CHOICE[,9]==1 ,9,3],bw=BW)$x
densidad.beta           <- density(marg.1.lambda[ CHOICE[,9]==1 ,9,3],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(marg.1.lambda[ CHOICE[,9]==1 ,9,3], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(marg.1.lambda[ CHOICE[,9]==1 ,9,3],xlim=lim_x,ylim=lim_y,main = "Alternativa auto Bus - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')




#TCAM
BW  <- bw.nrd(-marg.1.lambda[ CHOICE[,1]==1 ,1,4])
grilla.beta             <- density(-marg.1.lambda[ CHOICE[,1]==1 ,1,4],bw=BW)$x
densidad.beta           <- density(-marg.1.lambda[ CHOICE[,1]==1 ,1,4],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(-marg.1.lambda[ CHOICE[,1]==1 ,1,4], plot = FALSE)
lim_x <- c(hist.beta$breaks[11]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(-marg.1.lambda[ CHOICE[,1]==1 ,1,4],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como chofer)",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(-marg.1.lambda[ CHOICE[,2]==1 ,2,4])
grilla.beta             <- density(-marg.1.lambda[ CHOICE[,2]==1 ,2,4],bw=BW)$x
densidad.beta           <- density(-marg.1.lambda[ CHOICE[,2]==1 ,2,4],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(-marg.1.lambda[ CHOICE[,2]==1 ,2,4], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(-marg.1.lambda[ CHOICE[,2]==1 ,2,4],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como pasajero)",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(-marg.1.lambda[ CHOICE[,3]==1 ,3,4])
grilla.beta             <- density(-marg.1.lambda[ CHOICE[,3]==1 ,3,4],bw=BW)$x
densidad.beta           <- density(-marg.1.lambda[ CHOICE[,3]==1 ,3,4],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(-marg.1.lambda[ CHOICE[,3]==1 ,3,4], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(-marg.1.lambda[ CHOICE[,3]==1 ,3,4],xlim=lim_x,ylim=lim_y,main = "Alternativa taxi compartido",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(-marg.1.lambda[ CHOICE[,4]==1 ,4,4])
grilla.beta             <- density(-marg.1.lambda[ CHOICE[,4]==1 ,4,4],bw=BW)$x
densidad.beta           <- density(-marg.1.lambda[ CHOICE[,4]==1 ,4,4],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(-marg.1.lambda[ CHOICE[,4]==1 ,4,4], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(-marg.1.lambda[ CHOICE[,4]==1 ,4,4],xlim=lim_x,ylim=lim_y,main = "Alternativa Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(-marg.1.lambda[ CHOICE[,5]==1 ,5,4])
grilla.beta             <- density(-marg.1.lambda[ CHOICE[,5]==1 ,5,4],bw=BW)$x
densidad.beta           <- density(-marg.1.lambda[ CHOICE[,5]==1 ,5,4],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(-marg.1.lambda[ CHOICE[,5]==1 ,5,4], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(-marg.1.lambda[ CHOICE[,5]==1 ,5,4],xlim=lim_x,ylim=lim_y,main = "Alternativa Bus",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


BW  <- bw.nrd(-marg.1.lambda[ CHOICE[,6]==1 ,6,4])
grilla.beta             <- density(-marg.1.lambda[ CHOICE[,6]==1 ,6,4],bw=BW)$x
densidad.beta           <- density(-marg.1.lambda[ CHOICE[,6]==1 ,6,4],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(-marg.1.lambda[ CHOICE[,6]==1 ,6,4], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(-marg.1.lambda[ CHOICE[,6]==1 ,6,4],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como chofer) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(-marg.1.lambda[ CHOICE[,7]==1 ,7,4])
grilla.beta             <- density(-marg.1.lambda[ CHOICE[,7]==1 ,7,4],bw=BW)$x
densidad.beta           <- density(-marg.1.lambda[ CHOICE[,7]==1 ,7,4],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(-marg.1.lambda[ CHOICE[,7]==1 ,7,4], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(-marg.1.lambda[ CHOICE[,7]==1 ,7,4],xlim=lim_x,ylim=lim_y,main = "Alternativa auto (como pasajero) - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(-marg.1.lambda[ CHOICE[,8]==1 ,8,4])
grilla.beta             <- density(-marg.1.lambda[ CHOICE[,8]==1 ,8,4],bw=BW)$x
densidad.beta           <- density(-marg.1.lambda[ CHOICE[,8]==1 ,8,4],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(-marg.1.lambda[ CHOICE[,8]==1 ,8,4], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(-marg.1.lambda[ CHOICE[,8]==1 ,8,4],xlim=lim_x,ylim=lim_y,main = "Alternativa taxi compartido - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(-marg.1.lambda[ CHOICE[,9]==1 ,9,4])
grilla.beta             <- density(-marg.1.lambda[ CHOICE[,9]==1 ,9,4],bw=BW)$x
densidad.beta           <- density(-marg.1.lambda[ CHOICE[,9]==1 ,9,4],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(-marg.1.lambda[ CHOICE[,9]==1 ,9,4], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(-marg.1.lambda[ CHOICE[,9]==1 ,9,4],xlim=lim_x,ylim=lim_y,main = "Alternativa auto Bus - Metro",freq =FALSE ,xlab = "efecto marginal" ,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')


#histograms second part of problem
BW  <- bw.nrd(-lambda.ind[,1])
grilla.beta             <- density(-lambda.ind[,1],bw=BW)$x
densidad.beta           <- density(-lambda.ind[,1],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(-lambda.ind[,1], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(-lambda.ind[,1],xlim=lim_x,ylim=lim_y,main = "histograma para costo/tasa salarial",freq =FALSE ,xlab = "valor de parámetro por individuo" ,  breaks = 100,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(-lambda.ind[,2])
grilla.beta             <- density(-lambda.ind[,2],bw=BW)$x
densidad.beta           <- density(-lambda.ind[,2],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(-lambda.ind[,2], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(-lambda.ind[,2],xlim=lim_x,ylim=lim_y,main = "histograma para tiempo de viaje",freq =FALSE ,xlab = "valor de parámetro por individuo" ,  breaks = 100,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(-lambda.ind[,3])
grilla.beta             <- density(-lambda.ind[,3],bw=BW)$x
densidad.beta           <- density(-lambda.ind[,3],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(-lambda.ind[,3], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(-lambda.ind[,3],xlim=lim_x,ylim=lim_y,main = "histograma para tiempo de espera",freq =FALSE ,xlab = "valor de parámetro por individuo" ,  breaks = 100,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(-lambda.ind[,4])
grilla.beta             <- density(-lambda.ind[,4],bw=BW)$x
densidad.beta           <- density(-lambda.ind[,4],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(-lambda.ind[,4], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(-lambda.ind[,4],xlim=lim_x,ylim=lim_y,main = "histograma para tiempo de caminata",freq =FALSE ,xlab = "valor de parámetro por individuo" ,  breaks = 100,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

BW  <- bw.nrd(-lambda.ind[,5])
grilla.beta             <- density(-lambda.ind[,5],bw=BW)$x
densidad.beta           <- density(-lambda.ind[,5],bw=BW)$y
densidad.beta.upperband <- densidad.beta + 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
densidad.beta.lowerband <- densidad.beta - 1.96*1/sqrt(nobs*BW)*sqrt(densidad.beta*0.5)
hist.beta <- hist(-lambda.ind[,5], plot = FALSE)
lim_x <- c(hist.beta$breaks[1]-BW,hist.beta$breaks[length(hist.beta$breaks)]+BW)
lim_y <- c(0,ceiling(max(c(hist.beta$density,densidad.beta))))
hist.beta <- hist(-lambda.ind[,5],xlim=lim_x,ylim=lim_y,main = "histograma para autos/licencia",freq =FALSE ,xlab = "valor de parámetro por individuo" ,  breaks = 100,col  = "light blue")
lines(grilla.beta,densidad.beta,xlim=lim_x,ylim=lim_y,lty = 2, lwd = 2, col = 'red')

hist.CTOT_W   <-hist(lambda.ind[,1], main = "histograma para costo/tasa salarial", xlab = "valor de parámetro por individuo",  breaks = 100, col  = "light blue")
hist.TVIB     <- hist(lambda.ind[,2], main = "histograma para tiempo de viaje", xlab = "valor de parámetro por individuo",  breaks = 100, col  = "light blue")
hist.TESP     <- hist(lambda.ind[,3], main = "histograma para tiempo de espera", xlab = "valor de parámetro por individuo",  breaks = 100, col  = "light blue")
hist.TCAM     <-hist(lambda.ind[,4], main = "histograma para tiempo de caminata", xlab = "valor de parámetro por individuo",  breaks = 100, col  = "light blue")
hist.NAUTLIC  <-hist(lambda.ind[,5], main = "histograma para autos/licencia", xlab = "valor de parámetro por individuo", col  = "light blue")


#boxplot of SVOT per passenger (second part of problem).

bxplt.tivb  <-boxplot(lambda.ind[,2]/lambda.ind[,1])
tivb.ratio  <-lambda.ind[,2]/lambda.ind[,1]
summary(tivb.ratio)
summary(tivb.ratio[tivb.ratio > 0])
out.tivb    <-bxplt.tivb$out
tivb.final  <-tivb.ratio[which(!(tivb.ratio %in%  out.tivb) ) ]
summary(tivb.final)
boxplot(tivb.final)
length(tivb.ratio[tivb.ratio>0])/length(tivb.ratio)


bxplt.tesp  <-boxplot(lambda.ind[,3]/lambda.ind[,1])
tesp.ratio  <-lambda.ind[,3]/lambda.ind[,1]
summary(tesp.ratio)
summary(tesp.ratio[tesp.ratio > 0])
out.tesp    <-bxplt.tesp$out
tesp.final  <-tesp.ratio[which(!(tesp.ratio %in%  out.tesp) ) ]
summary(tesp.final)
boxplot(tesp.final)
length(tesp.ratio[tesp.ratio>0])/length(tesp.ratio)


bxplt.tcam  <-boxplot(lambda.ind[,4]/lambda.ind[,1])
tcam.ratio  <-lambda.ind[,4]/lambda.ind[,1]
summary(tcam.ratio)
summary(tcam.ratio[tcam.ratio > 0])
out.tcam    <-bxplt.tcam$out
tcam.final  <-tcam.ratio[which(!(tcam.ratio %in%  out.tcam) ) ]
summary(tcam.final)
boxplot(tcam.final)
length(tcam.ratio[tcam.ratio>0])/length(tcam.ratio)


SVOT<-data.frame(lambda.ind[,2:4]/lambda.ind[,1])
names(SVOT) <-c("SVOT.TIVB", "SVOT.TESP", "SVOT.TCAM")
boxplot(SVOT)



  
SVOT_FINAL<-data.frame(tivb.ratio[-c(578)], 
                       tesp.ratio[-c(578)], 
                       tcam.ratio[-c(578)])
names(SVOT_FINAL) <-c("SVOT.TIVB", "SVOT.TESP", "SVOT.TCAM")
boxplot(SVOT_FINAL)



#------------------------mean and sd categorized for comuna------------------------

mean.vst<-array(0,dim = c(nalt,3,2))

for(i in 1:nalt){
  for(j in 2:4){
    mean.vst[i, (j-1),1]<-mean(marg.1.lambda[CHOICE[,i] ==1 & dframe$LasCondes ==0,i,j]/marg.1.lambda[CHOICE[,i] ==1 & dframe$LasCondes ==0,i,1])
    mean.vst[i,(j-1),2]<-mean(marg.1.lambda[CHOICE[,i] ==1 & dframe$LasCondes ==1,i,j]/marg.1.lambda[CHOICE[,i] ==1 & dframe$LasCondes ==1,i,1])
  }
}

mean.vst.2 <-array(0,dim = c(nalt,3,2))

for(i in 1:nalt){
  for(j in 2:4){
    mean.vst.2[i, (j-1),1]<-mean(marg.1.lambda[DISP[,i] ==1 & dframe$LasCondes ==0,i,j])/mean(marg.1.lambda[DISP[,i] ==1 & dframe$LasCondes ==0,i,1])
    mean.vst.2[i,(j-1),2]<-mean(marg.1.lambda[DISP[,i] ==1 & dframe$LasCondes ==1,i,j])/mean(marg.1.lambda[DISP[,i] ==1 & dframe$LasCondes ==1,i,1])
  }
}

mean.vst.3<-matrix(0,nalt,3)

for(i in 1:nalt){
  for(j in 2:4){
    mean.vst.3[i, (j-1)]<-mean(marg.1.lambda[CHOICE[,i] ==1 ,i,j]/marg.1.lambda[CHOICE[,i] ==1 ,i,1])
  }
}




median.vst<-array(0,dim = c(nalt,3,2))

for(i in 1:nalt){
  for(j in 2:4){
    median.vst[i, (j-1),1]<-median(marg.1.lambda[CHOICE[,i] ==1 & dframe$LasCondes ==0,i,j])/median(marg.1.lambda[CHOICE[,i] ==1 & dframe$LasCondes ==0,i,1])
    median.vst[i,(j-1),2]<-median(marg.1.lambda[CHOICE[,i] ==1 & dframe$LasCondes ==1,i,j])/median(marg.1.lambda[CHOICE[,i] ==1 & dframe$LasCondes ==1,i,1])
  }
}


sd.vst<-array(0,dim = c(nalt,3,2))

for(i in 1:nalt){
  for(j in 2:4){
    sd.vst[i, (j-1),1]<-sd(marg.1.lambda[CHOICE[,i] ==1 & dframe$LasCondes ==0,i,j]/marg.1.lambda[CHOICE[,i] ==1 & dframe$LasCondes ==0,i,1])
    sd.vst[i,(j-1),2]<-sd(marg.1.lambda[CHOICE[,i] ==1 & dframe$LasCondes ==1,i,j]/marg.1.lambda[CHOICE[,i] ==1 & dframe$LasCondes ==1,i,1])
  }
}


for(i in 1:697){
  for(j in 1:nalt){
    if(is.nan(svot.tesp.condes[i,j])){svot.tesp.condes[i,j]<-0}
    }
}


mean(marg.1.lambda[ marg.1.lambda[,,3] >0,,3])/mean(marg.1.lambda[ marg.1.lambda[,,1] >0,,1])

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
