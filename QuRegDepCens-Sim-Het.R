

################################################################################
# This file contains code for simulations in the heteroscedastic scenario of   #
#                                                                              #
# D'Haen, M., Van Keilegom, I., and Verhasselt, A. (2025), Quantile regression #
# under dependent censoring with unknown association. Lifetime Data Analysis,  #
# 31(2):253--299.                                                              #
#                                                                              #
# Code author: Myrthe D'Haen                                                   #
# Last revised on: 07/02/2024                                                  #
#                                                                              #
################################################################################



## All settings are to be specified in PART 0 below (lines 23-119),
# rest of the code needs not be altered

## Settings in this file assume: sigma_T is heterosk., exp. (any combinations
# true-test copula possible: dep-dep / dep-indep / indep - dep / indep-indep)

############ PART 0: SETTINGS SPECIFICATION ###################################

### external storage
simulation_name <- "Sim_scen1_het"
folder_path <- paste0("G:/My Drive/QuRegDepCens/", simulation_name)
DigNum <- 6 # number of digits used for printing


### simulation settings
simulation_size <- 200
sample_size = 500
quantile_levels <- c(0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 0.25, 0.75)


### basic seed for all randomised operations (for reproducibility)
# supply a number (same as in some results to be verified), or put to FALSE in
# order to have a new, random one generated.
basic_seed <- FALSE


### optimisation & test settings
init_value_number_basis <- 50
init_value_number_intermed <- 20
init_value_number_final <- 50

it_NM <- 500
it_NMCob_unconstr <- 400
it_NMCob_constr <- 100

lag_deg_upper <- 4
lower_bound_on_phis <- -2
upper_bound_on_phis <- 2

test_cop_name = "frank"


### data generation settings
true_cop_name = "frank" # if "indep", put true_ktau = 0
true_ktau <- 0.5

## scenario 1
# true distribution for T
true_beta_0 <- 2.8
true_beta_T <- c(0.6)
true_gam_par <- c(-1.5, 0.45)

true_distr_T <- "norm"

# true distribution for C (always normal)
true_alpha_0 <- 3.15
true_alpha_C <- c(0.45)
true_sigma_C <- 0.8

# covariate distribution
X_dimension <- 1
X_distribution <- "unif"
X_lower <- 0
X_upper <- 4

# covariates for which the quantile predictions are computed and stored
X_selection_size <- 9
X_selection <- as.matrix(cbind(rep(1, 9),
                               c(0.25, 0.5, 1, 1.5, 2, 2.5, 3, 3.5, 3.75)),
                         ncol = 2, byrow = TRUE)



# ## scenario 2
# # true distribution for T
# true_beta_0 <- 2.6
# true_beta_T <- c(0.7)
# true_gam_par <- c(-2.4,0.2)
# 
# true_distr_T <- "EAL"
# 
# true_lambda <- 0.3
# true_phi_til <- c(-0.3, 0.2)
# true_phi <- c(-0.15)
# 
# # true distribution for C (always normal)
# true_alpha_0 <- 3
# true_alpha_C <- c(0.45)
# true_sigma_C <- 0.65

# # covariate distribution
# X_dimension <- 1
# X_distribution <- "norm"
# X_mean <- 0.5
# X_var <- 1

# # covariates for which the quantile predictions are computed and stored
# X_selection_size <- 15
# X_selection <- as.matrix(cbind(rep(1, 15),
#                                c(-2, -1.5, -1, -0.5, -0.25, 0, 0.25, 0.5,
#                                  0.75, 1, 1.25, 1.5, 2, 2.5,3)),
#                          ncol = 2, byrow = TRUE)
############ PART 0: END ######################################################





############ PART 1: LIBRARIES & FUNCTIONS ####################################
library(orthopolynom)
library(tictoc)
library(rvinecopulib)
library(nloptr)
library(MASS) # for multivariate covariate sampling
library(Hmisc) # for tidy printing


################ Auxiliary values & functions #################################

## Heteroskedasticity for T ###
sigma_fun <- function(X,gam){
  return(exp(X %*% gam))
}

sqnorm <- function(vect){
  return(sum(vect^2))
}

Lag_coeff <- function(n,j){
  choose(n,j)*(-1)^j/factorial(j)
}


# perturbation: multiply by random factors between 1/2 and 2
perturb <- function(x, seed){
  set.seed(seed)
  return(x*runif(length(x), 0.5, 2))
}

# slight perturbation: multiply by random factors between 2/3 ans 4/3
slight_perturb <- function(x, seed){
  set.seed(seed)
  return(x*runif(length(x), 2/3, 4/3))
}



# partial derivatives of h-functions (faster than using hbicop).
# Avoid getting values outside (0,1)
h_TC_frank <- function(u,v,theta){
  res <- (exp(-theta*v)*(exp(-theta*u) - 1))/
    (exp(-theta) - 1 + (exp(-theta*u) - 1)*(exp(-theta*v) - 1))
  return(pmax(pmin(res, 0.99999),0.00001))
}
h_CT_frank <- function(u,v,theta){
  res <- (exp(-theta*u)*(exp(-theta*v) - 1))/
    (exp(-theta) - 1 + (exp(-theta*v) - 1)*(exp(-theta*u) - 1))
  return(pmax(pmin(res, 0.99999),0.00001))
}

h_TC_gumbel <- function(u,v,theta){
  res <- ((log(u)/log(v))^theta+1)^(-1 + 1/theta)*
    exp(-log(v) -((-log(u))^theta + (-log(v))^theta)^(1/theta))
  return(pmax(pmin(res, 0.99999),0.00001))
}

h_CT_gumbel <- function(u,v,theta){
  res <- ((log(v)/log(u))^theta+1)^(-1 + 1/theta)*
    exp(-log(u) -((-log(v))^theta + (-log(u))^theta)^(1/theta))
  return(pmax(pmin(res, 0.99999),0.00001))
}

h_TC_clayton <- function(u,v,theta){
  res <- (1 + (v/u)^theta - v^theta)^(-(theta+1)/theta)
  return(pmax(pmin(res, 0.99999),0.00001))
}

h_CT_clayton <- function(u,v,theta){
  res <- (1 + (u/v)^theta - u^theta)^(-(theta+1)/theta)
  return(pmax(pmin(res, 0.99999),0.00001))
}

## To sample covariates of the specified distribution for X ##
# already includes column of 1's for intercept.
covariate_sampling <- function(size, seed){
  set.seed(seed)
  if (X_distribution == "norm"){
    return(cbind(1, mvrnorm(n = size, mu = X_mean,
                            Sigma = matrix(X_var, byrow = TRUE,
                                           nrow = X_dimension))))
  }
  if (X_distribution == "unif"){
    return(cbind(1, runif(n = size, X_lower, X_upper)))
  }
}
###############################################################################


######## Data-driven initial value determination ##############################
# note: always includes initial value for eta (~ ktau) too, that is afterwards
# dropped in the independence case


# determines list of init_value_number_basis (data-driven) initial values, but no
# phi_tilde or phi is present
determine_init_basis <- function(T1,X1,C0,X0,Delta){
  
  ## data-driven part: beta, gamma and paras_C ##
  
  # initial parameters for beta and paras_C
  # X already has intercept column: ~ X - 1
  alpha_init <- as.vector(lm(C0 ~ X0 - 1)$coefficients)
  beta_init <- as.vector(lm(T1 ~ X1 - 1)$coefficients)
  
  C_res <- C0 - as.matrix(X0) %*% alpha_init
  sigma_C_init <- sd(C_res)
  
  # to get an approximate value for gamma
  Z <- (T1 - X1 %*% beta_init)^2
  # avoid near-zero values
  Z[Z < 10^(-100)] <- rep(10^(-100), length((Z[Z < 10^(-100)])))
  gamma_init <- as.vector(lm(log(Z) ~ X1 -1)$coefficients/2)
  gamma_init_update <- c(gamma_init[1] - log(8)/2, gamma_init[-1])
  
  # used further on in loop for adjusting beta_0
  T_res_no_intercept <- T1 - as.matrix(X1[,-1]) %*% beta_init[-1]
  
  ## other parameters: random values in admissible/some plausible range
  init_values <- vector(mode = "list", length = init_value_number_basis)
  
  for (j in 1:init_value_number_basis){
    set.seed(init_seeds[1] + j)
    lambda_init <- runif(n = 1, min = 0.05, max = 0.95)
    transf_lambda_init <- lambda_transform(lambda_init)
    
    # adjust beta_0 based on the current initial value for lambda #
    beta_intercept <- as.numeric(quantile(T_res_no_intercept, lambda_init))
    beta_init_update <- c(beta_intercept, beta_init[-1])
    
    set.seed(init_seeds[2] + j)
    if (test_cop_name == "frank"){ # ktau between -1 and 1
      eta_init <- ktau_to_eta(ktau = runif(1, -1, 1), cop_name = test_cop_name)
    }
    if (test_cop_name == "gumbel"){ # ktau between 0 and 1
      eta_init <- ktau_to_eta(ktau = runif(1,0,1), cop_name = test_cop_name)
    }
    if (test_cop_name == "clayton"){ # ktau between 0 and 1
      eta_init <- ktau_to_eta(ktau = runif(1,0,1), cop_name = test_cop_name)
    }
    if (test_cop_name == "indep"){
      eta_init <- 0 # not used during optimisation anyway
    }
    
    init_values[[j]] <- c(eta_init, perturb(beta_init_update, init_seeds[3] + j),
                          perturb(gamma_init_update, init_seeds[4] + j),
                          transf_lambda_init,
                          perturb(alpha_init, init_seeds[5] + j),
                          log(perturb(sigma_C_init, init_seeds[6] + j)))
  }
  return(init_values)
}

# determines list of init_value_number_final values, all only slight
# perturbations of the current parameter estimates
determine_init_final <- function(current_paras, indep_assumption = FALSE){
  new_init_values <- vector(mode = "list", length = init_value_number_final)
  if (! indep_assumption){
    for (j in seq_len(init_value_number_final)){
      new_init_values[[j]] <- slight_perturb(x = current_paras,
                                             seed = init_seeds[7] + j)
    }
  } else {
    for (j in seq_len(init_value_number_final)){
      new_init_values[[j]] <- c(0,slight_perturb(x = current_paras,
                                                 seed = init_seeds[8] + j))
    }
  }
  return(new_init_values)
}
###############################################################################


########## Censoring functions: density, distribution and quantile ############
# standard normal of (Y - alpha^T*X), homosk. scaling
dCens <- function(y,x, transf_paras_C){
  alpha <- transf_paras_C[-length(transf_paras_C)]
  s <- exp(transf_paras_C[length(transf_paras_C)])
  z <- 1/s*(y -  x %*% alpha)
  return(1/s*dnorm(z))
}

pCens <- function(y,x, transf_paras_C){
  alpha <- transf_paras_C[-length(transf_paras_C)]
  s <- exp(transf_paras_C[length(transf_paras_C)])
  z <- 1/s*(y -  x %*% alpha)
  return(pnorm(z))
}

qCens <- function(w,x, transf_paras_C){
  alpha <- transf_paras_C[-length(transf_paras_C)]
  s <- exp(transf_paras_C[length(transf_paras_C)])
  return(qnorm(w)*s + x %*% alpha)
}
###############################################################################


############ Transformation functions #########################################
### (i) eta <-> ktau -> theta
eta_to_ktau <- function(eta, cop_name){
  if (cop_name == "frank"){ # ktau between -1 and 1
    ktau <- tanh(eta)
  }
  if (cop_name == "gumbel") { # ktau between 0 and 1
    ktau <- 1/(1 + exp(-eta))
  }
  if (cop_name == "clayton") { # ktau between 0 and 1
    ktau <- 1/(1 + exp(-eta))
  }
  if (cop_name == "indep"){ # no ktau present
    ktau <- 0
  }
  return(ktau)
}


ktau_to_eta <- function(ktau, cop_name){
  if (cop_name == "frank"){ # ktau between -1 and 1
    eta <- 0.5* log((1 + ktau)/(1 - ktau))
  }
  if (cop_name == "gumbel"){ # ktau between 0 and 1
    eta <- log(ktau/(1 - ktau))
  }
  if (cop_name == "clayton"){ # ktau between 0 and 1
    eta <- log(ktau/(1 - ktau))
  }
  if (cop_name == "indep"){ # no ktau present
    eta <- 0
  }
  return(eta)
}

ktau_to_theta <- function(ktau, cop_name){
  theta <- as.numeric(ktau_to_par(family = cop_name,
                                  tau = ktau))
  return(theta)
}


### (ii) lambda <-> transformed lambda,
lambda_transform <- function(lambda){
  return(log(lambda/(1 - lambda)))
}

lambda_inverse_transform <- function(transf_lambda){
  return(1/(1 + exp(-transf_lambda)))
}


### (iii) summary function for transformations on all parameters
para_inv_transform <- function(transf_para_vec, cop_name){
  para_vec <- transf_para_vec
  
  if (cop_name == "indep"){
    ktau_length <- 0
  } else {
    ktau_length <- 1
  }
  
  # replace eta by ktau, if present
  if (ktau_length == 1){
    para_vec[1] <- eta_to_ktau(eta = para_vec[1], cop_name = cop_name)
  }
  
  # replace transf_lambda by lambda
  para_vec[lambda_index + ktau_length] <- lambda_inverse_transform(
    para_vec[lambda_index + ktau_length])
  
  # replace log_sigma_C by sigma_C
  para_vec[length(para_vec)] <- exp(para_vec[length(para_vec)])
  
  return(para_vec)
}
###############################################################################


############ EAL functions: density, distribution and (numerical) quantile ####
dEAL <- function(y, x, beta, gam_par, lambda, phi_til, phi){
  
  s <- sigma_fun(x, gam_par)
  z <- 1/s * (y - x %*% beta)
  
  phi_til_ext <- c(1, phi_til)
  phi_ext <- c(1, phi)
  
  # Lag of degree 0 is constant 1, so first term in sum is always fixed constant
  left_sum <- 1
  right_sum <- 1
  
  poly_list <- laguerre.polynomials(max(length(phi),length(phi_til)),
                                    normalized = TRUE)
  
  if (length(y) == 1){# avoid indexing one vector x as x[pos_indices,]
    if (z <= 0){
      for (k in seq_along(phi_til)){
        poly <- as.function(poly_list[[k+1]])
        left_sum <- left_sum + phi_til[k]*poly((lambda-1)*z)
      }
      result <- (1-lambda)*lambda/s*1/sqnorm(phi_til_ext)*exp(-z *(lambda-1)) * left_sum^2
      
    } else {
      for (k in seq_along(phi)){
        poly <- as.function(poly_list[[k+1]])
        right_sum <- right_sum + phi[k]*poly(lambda*z)
      }
      result <- lambda*(1-lambda)/s*1/sqnorm(phi_ext)*exp(-z*lambda) * right_sum^2
    }
  } else {
    pos_indices <- which(z > 0)
    z_pos <- z[pos_indices]
    z_neg <- z[-pos_indices]
    s_pos <- s[pos_indices]
    s_neg <- s[-pos_indices]
    
    for (k in seq_along(phi_til)){
      poly <- as.function(poly_list[[k+1]])
      left_sum <- left_sum + phi_til[k]*poly((lambda-1)*z_neg)
    }
    
    for (k in seq_along(phi)){
      poly <- as.function(poly_list[[k+1]])
      right_sum <- right_sum + phi[k]*poly(lambda*z_pos)
    }
    
    result <- rep(0, length(z))
    result[pos_indices] <- lambda*(1-lambda)/s_pos*1/sqnorm(phi_ext)*
      exp(-z_pos*lambda) * right_sum^2
    result[-pos_indices] <- (1-lambda)*lambda/s_neg*1/sqnorm(phi_til_ext)*
      exp(-z_neg *(lambda-1)) * left_sum^2
  }
  return(as.matrix(result))
}

pEAL_neg <- function(y, x, beta, gam_par, lambda, phi_til){
  
  s <- sigma_fun(x, gam_par)
  z <- 1/s * (y - x %*% beta)
  
  phi_til_ext <- c(1, phi_til)
  n <- length(phi_til)
  
  sum <- 0
  for (a in 0:n){
    for (b in 0:n){
      for (c in 0:a){
        for (d in 0:b){
          inner_sum <- 0
          for (j in 0:(c+d)){
            inner_sum <- inner_sum + factorial(c+d)/factorial(j)*
              (-(1-lambda)*z)^j
          }
          sum <- sum + phi_til_ext[a+1]*phi_til_ext[b+1] *
            Lag_coeff(a,c)*Lag_coeff(b,d)* inner_sum
        }
      }
    }
  }
  res <- lambda*exp((1-lambda)*z) * sum/sqnorm(phi_til_ext)
  
  res_corrected <- pmin(pmax(0, res), 1)
  return(res_corrected) # could still be NaN !
}

pEAL_pos <- function(y, x, beta, gam_par, lambda, phi){
  
  s <- sigma_fun(x, gam_par)
  z <- 1/s * (y - x %*% beta)
  
  phi_ext <- c(1, phi)
  n <- length(phi)
  
  sum <- 0
  for (a in 0:n){
    for (b in 0:n){
      for (c in 0:a){
        for (d in 0:b){
          inner_sum <- 0
          for (j in 0:(c+d)){
            inner_sum <- inner_sum + factorial(c+d)/factorial(j)*(lambda*z)^j
          }
          sum <- sum + phi_ext[a+1]*phi_ext[b+1]*Lag_coeff(a,c)*Lag_coeff(b,d)*
            (factorial(c+d)- exp(-lambda*z)*inner_sum)
        }
      }
    }
  }
  res <- lambda + (1-lambda) * sum/sqnorm(phi_ext)
  
  res_corrected <- pmin(pmax(0, res), 1)
  return(res_corrected) # could still be NaN !
}

pEAL <- function(y, x, beta, gam_par, lambda, phi_til, phi){
  s <- sigma_fun(x, gam_par)
  z <- 1/s * (y - x %*% beta)
  
  
  if (length(y) == 1){# avoid indexing one vector x as x[pos_indices,]
    if (z < 0){
      res_vec <- pEAL_neg(y, x, beta, gam_par, lambda, phi_til)
    } else {
      res_vec <- pEAL_pos(y, x, beta, gam_par, lambda, phi)
    }
  } else { # general case, correct subsetting dimensions
    pos_indices <- which(z > 0)
    res_vec <- as.matrix(rep(0, length(z)))
    
    if (length(pos_indices) == 0){
      res_vec <- pEAL_neg(y, x, beta, gam_par, lambda, phi_til)
    } else {
      res_vec[pos_indices,] <- pEAL_pos(y[pos_indices], x[pos_indices,],
                                        beta, gam_par, lambda, phi)
      
      
      if (length(pos_indices) < length(z)){
        res_vec[-pos_indices,] <- pEAL_neg(y[-pos_indices], x[-pos_indices,],
                                           beta, gam_par, lambda, phi_til)
      }
    }
  }
  
  # correct for numerical errors that lead to values outside [0,1]
  res_vec <- pmin(pmax(0, res_vec), 1)
  
  return(as.matrix(res_vec)) # could still be NaN !
}

qEAL <- function(w, x, beta, gam_par, lambda, phi_til, phi){
  
  # determine basis quantile from EAL, only afterwards shift
  x_null = matrix(rep(1, length(w)*(X_dimension + 1)), nrow = length(w))
  beta_null = rep(0, X_dimension + 1)
  gam_par_null = rep(0, X_dimension + 1)
  
  f_null <- function(y){
    return(pEAL(y, x_null, beta_null, gam_par_null, lambda, phi_til, phi) - w)
  }
  
  basis_quantile <- uniroot(f_null, lower = -10, upper = 10, extendInt = "yes")$root
  
  s <- sigma_fun(x, gam_par)
  
  return(x %*% beta + s*basis_quantile)
}
###############################################################################


############ (Partial) likelihood & optimisation functions ####################
# all functions here assume that parameters are supplied in transformed version

###### Likelihood optimisation over all parameters ######

log_lik_fun <- function(all_paras, lag_degs, cop_name, Y, X, Delta){
  
  # 1) Retrieving current parameters & corresponding copula object ----
  
  paras_T_indices <- c(beta_full_index, gamma_index, lambda_index,
                       phi_til_index(lag_degs),
                       phi_index(lag_degs)) + 1 # omit eta (present here by
  # assumption, in other cases, log_lik_fun_indep is used)
  
  eta <- all_paras[1]
  transf_paras_T <- all_paras[paras_T_indices]
  transf_paras_C <- all_paras[-c(1, paras_T_indices)]
  
  beta_full <- transf_paras_T[beta_full_index]
  transf_lam <- transf_paras_T[lambda_index]
  gam_par <- transf_paras_T[gamma_index]
  phi_til <- transf_paras_T[phi_til_index(lag_degs)]
  phi <- transf_paras_T[phi_index(lag_degs)]
  
  lambda <- lambda_inverse_transform(transf_lam)
  # ----
  
  # 2) Construct argument matrices for censored & uncensored cases ----
  Y_un <- Y[Delta == 1]
  Y_cens <- Y[Delta == 0]
  
  X_un <- X[Delta == 1, ]
  X_cens <- X[Delta == 0, ]
  
  # ----
  
  # 3) Density, distribution & copula partial derivative evaluation ----
  
  ## density
  dens_T_un <- dEAL(Y_un, X_un, beta_full, gam_par, lambda, phi_til, phi)
  dens_C_cens <- dCens(Y_cens, X_cens, transf_paras_C)
  
  ## distribution
  distr_T_un <- pEAL(Y_un, X_un, beta_full, gam_par, lambda, phi_til, phi)
  distr_T_cens <- pEAL(Y_cens, X_cens, beta_full, gam_par, lambda, phi_til, phi)
  
  distr_C_un <- pCens(Y_un, X_un, transf_paras_C)
  distr_C_cens <- pCens(Y_cens, X_cens, transf_paras_C)
  
  
  ## copula partial derivatives
  theta <- ktau_to_theta(eta_to_ktau(eta, cop_name), cop_name)
  
  if (cop_name == "frank"){
    h_C_given_T_uncens <- h_CT_frank(u = distr_T_un, v = distr_C_un, theta)
    h_T_given_C_cens <- h_TC_frank(u = distr_T_cens, v = distr_C_cens, theta)
  }
  if (cop_name == "gumbel"){
    h_C_given_T_uncens <- h_CT_gumbel(u = distr_T_un, v = distr_C_un, theta)
    h_T_given_C_cens <- h_TC_gumbel(u = distr_T_cens, v = distr_C_cens, theta)
  }
  if (cop_name == "clayton"){
    h_C_given_T_uncens <- h_CT_clayton(u = distr_T_un, v = distr_C_un, theta)
    h_T_given_C_cens <- h_TC_clayton(u = distr_T_cens, v = distr_C_cens, theta)
  }
  # ----
  
  lh_uncens <- dens_T_un * (1 - h_C_given_T_uncens)
  lh_cens <- dens_C_cens * (1 - h_T_given_C_cens)
  
  llh <- sum(log(lh_uncens)) + sum(log(lh_cens))
  
  res <- min(max(llh, -100000), 100000) # avoid returning +- Inf
  if (is.nan(res)){ # avoid NaN (due to Inf - Inf by num. errors) as well
    res <- -100000
  }
  return(res) 
}

# exactly the same as previous function, but now returning minus the result
neg_log_lik_fun <- function(all_paras, lag_degs, cop_name, Y, X, Delta){
  
  # 1) Retrieving current parameters & corresponding copula object ----
  
  paras_T_indices <- c(beta_full_index, gamma_index, lambda_index,
                       phi_til_index(lag_degs),
                       phi_index(lag_degs)) + 1 # omit eta (present here by
  # assumption, in other cases, log_lik_fun_indep is used)
  
  eta <- all_paras[1]
  transf_paras_T <- all_paras[paras_T_indices]
  transf_paras_C <- all_paras[-c(1, paras_T_indices)]
  
  beta_full <- transf_paras_T[beta_full_index]
  transf_lam <- transf_paras_T[lambda_index]
  gam_par <- transf_paras_T[gamma_index]
  phi_til <- transf_paras_T[phi_til_index(lag_degs)]
  phi <- transf_paras_T[phi_index(lag_degs)]
  
  lambda <- lambda_inverse_transform(transf_lam)
  # ----
  
  # 2) Construct argument matrices for censored & uncensored cases ----
  Y_un <- Y[Delta == 1]
  Y_cens <- Y[Delta == 0]
  
  X_un <- X[Delta == 1, ]
  X_cens <- X[Delta == 0, ]
  
  # ----
  
  # 3) Density, distribution & copula partial derivative evaluation ----
  
  ## density
  dens_T_un <- dEAL(Y_un, X_un, beta_full, gam_par, lambda, phi_til, phi)
  dens_C_cens <- dCens(Y_cens, X_cens, transf_paras_C)
  
  ## distribution
  distr_T_un <- pEAL(Y_un, X_un, beta_full, gam_par, lambda, phi_til, phi)
  distr_T_cens <- pEAL(Y_cens, X_cens, beta_full, gam_par, lambda, phi_til, phi)
  
  distr_C_un <- pCens(Y_un, X_un, transf_paras_C)
  distr_C_cens <- pCens(Y_cens, X_cens, transf_paras_C)
  
  
  ## copula partial derivatives
  theta <- ktau_to_theta(eta_to_ktau(eta, cop_name), cop_name)
  
  if (cop_name == "frank"){
    h_C_given_T_uncens <- h_CT_frank(u = distr_T_un, v = distr_C_un, theta)
    h_T_given_C_cens <- h_TC_frank(u = distr_T_cens, v = distr_C_cens, theta)
  }
  if (cop_name == "gumbel"){
    h_C_given_T_uncens <- h_CT_gumbel(u = distr_T_un, v = distr_C_un, theta)
    h_T_given_C_cens <- h_TC_gumbel(u = distr_T_cens, v = distr_C_cens, theta)
  }
  if (cop_name == "clayton"){
    h_C_given_T_uncens <- h_CT_clayton(u = distr_T_un, v = distr_C_un, theta)
    h_T_given_C_cens <- h_TC_clayton(u = distr_T_cens, v = distr_C_cens, theta)
  }
  # ----
  
  lh_uncens <- dens_T_un * (1 - h_C_given_T_uncens)
  lh_cens <- dens_C_cens * (1 - h_T_given_C_cens)
  
  llh <- sum(log(lh_uncens)) + sum(log(lh_cens))
  
  res <- min(max(llh, -100000), 100000) # avoid returning +- Inf
  if (is.nan(res)){ # avoid NaN (due to Inf - Inf by num. errors) as well
    res <- -100000
  }
  return(-res) 
}

ctuity_constr_fun <- function(all_paras, lag_degs,
                              cop_name, Y, X, Delta){
  # args. on second line not needed, but should be the same as for obj. fun.
  
  phi_til <- all_paras[phi_til_index(lag_degs) + 1] # omit eta
  phi <- all_paras[phi_index(lag_degs) + 1] # omit eta
  
  phi_til_ext <- c(1, phi_til)
  phi_ext <- c(1, phi)
  
  # combination of Lag. polynomials evaluated in 0 on neg./pos. axis:
  left <- sum(phi_til_ext)^2 / sqnorm(phi_til_ext)
  right <- sum(phi_ext)^2 / sqnorm(phi_ext)
  
  jump <- left - right
  
  return(c(jump, - jump))
}

### perform mll estimation using the specified method and settings,
# return list(estimated mll value, corresponding parameter estimates)###
perform_mll_optimisation <- function(lag_degs, cop_name, Y, X, Delta,
                                     init_val_list,
                                     opt_algo, it_num_constr, it_num_unconstr,
                                     indep_assumption = FALSE){
  
  current_mllh <- -100000
  current_paras <- init_val_list[[1]]
  
  if (opt_algo == "NM"){
    if (indep_assumption){
      for (init_vals in init_val_list){
        res <- optim(init_vals[-1], log_lik_fun_indep, method = "Nelder-Mead",
                     control = list(fnscale = -1, maxit = it_num_unconstr),
                     lag_degs = lag_degs, cop_name = cop_name,
                     Y = Y, X = X, Delta = Delta)
        new_paras <- res[[1]]
        new_mllh <- res[[2]]
        
        if (new_mllh > current_mllh){
          current_mllh <- new_mllh
          current_paras <- new_paras
        }
      }
    } else {
      for (init_vals in init_val_list){
        res <- optim(init_vals, log_lik_fun, method = "Nelder-Mead",
                     control = list(fnscale = -1, maxit = it_num_unconstr),
                     lag_degs = lag_degs, cop_name = cop_name,
                     Y = Y, X = X, Delta = Delta)
        new_paras <- res[[1]]
        new_mllh <- res[[2]]
        
        if (new_mllh > current_mllh){
          current_mllh <- new_mllh
          current_paras <- new_paras
        }
      }
    }
  }
  
  
  if (opt_algo == "NMCob"){
    opts <- list("algorithm"= "NLOPT_LN_COBYLA", "maxeval"= it_num_constr)
    
    if (indep_assumption){
      for (init_vals in init_val_list){
        intermed_para <- optim(init_vals[-1], log_lik_fun_indep,
                               method = "Nelder-Mead",
                               control = list(fnscale = -1,
                                              maxit = it_num_unconstr),
                               lag_degs = lag_degs, cop_name = cop_name,
                               Y = Y, X = X, Delta = Delta)$par
        
        res <- nloptr(x0 = intermed_para,
                      eval_f = neg_log_lik_fun_indep, # max. rather than min.!
                      eval_g_ineq = ctuity_constr_fun_indep,
                      opts = opts,
                      lag_degs = lag_degs, cop_name = cop_name,
                      Y = Y, X = X, Delta = Delta)
        new_paras <- res$solution
        new_mllh <- - res$objective # Compare with llh rather than neg_llh
        
        if (new_mllh > current_mllh){
          current_mllh <- new_mllh
          current_paras <- new_paras
        }
      }
    } else {
      for (init_vals in init_val_list){
        intermed_para <- optim(init_vals, log_lik_fun,
                               method = "Nelder-Mead",
                               control = list(fnscale = -1,
                                              maxit = it_num_unconstr),
                               lag_degs = lag_degs, cop_name = cop_name,
                               Y = Y, X = X, Delta = Delta)$par
        
        res <- nloptr(x0 = intermed_para,
                      eval_f = neg_log_lik_fun, # max. rather than min.!
                      eval_g_ineq = ctuity_constr_fun,
                      opts = opts,
                      lag_degs = lag_degs, cop_name = cop_name,
                      Y = Y, X = X, Delta = Delta)
        new_paras <- res$solution
        new_mllh <- - res$objective # Compare with llh rather than neg_llh
        
        if (new_mllh > current_mllh){
          current_mllh <- new_mllh
          current_paras <- new_paras
        }
      }
    }
  }
  
  return(list(current_mllh, current_paras))
}

###############################################################################

###### Likelihood optimisation while fixing some of the parameters ######
log_lik_partial <- function(para_variable, para_fixed, fixed_indices,
                            lag_degs, cop_name, Y, X, Delta){
  all_paras <- rep(0, length(para_variable) + length(para_fixed))
  all_paras[fixed_indices] <- para_fixed
  all_paras[-fixed_indices] <- para_variable
  return(log_lik_fun(all_paras, lag_degs, cop_name, Y, X, Delta))
}

neg_log_lik_partial <- function(para_variable, para_fixed, fixed_indices,
                                lag_degs, cop_name, Y, X, Delta){
  all_paras <- rep(0, length(para_variable) + length(para_fixed))
  all_paras[fixed_indices] <- para_fixed
  all_paras[-fixed_indices] <- para_variable
  return(-log_lik_fun(all_paras, lag_degs, cop_name, Y, X, Delta))
}

ctuity_constr_partial <- function(para_variable, para_fixed, fixed_indices,
                                  lag_degs, cop_name, Y, X, Delta){
  # not all arguments needed, but should be the same as for obj. fun.
  
  if (cop_name == "indep"){
    ktau_length <- 0
  } else {
    ktau_length <- 1
  }
  
  all_paras <- rep(0, length(para_variable) + length(para_fixed))
  all_paras[fixed_indices] <- para_fixed
  all_paras[-fixed_indices] <- para_variable
  
  phis <- all_paras[c(phi_til_index(lag_degs), phi_index(lag_degs))
                    + ktau_length]
  
  if (lag_degs[1] == 0){
    phi_til_ext <- c(1)
    phi_ext <- c(1, phis)
  } else {
    if (lag_degs[2] == 0){
      phi_til_ext <- c(1, phis)
      phi_ext <- c(1)
    } else {
      phi_til_ext <- c(1, phis[1:lag_degs[1]])
      phi_ext <- c(1, phis[(lag_degs[1]+1):(lag_degs[1] + lag_degs[2])])
    }
  }
  
  # combination of Lag. polynomials evaluated in 0 on neg./pos. axis:
  left <- sum(phi_til_ext)^2 / sqnorm(phi_til_ext)
  right <- sum(phi_ext)^2 / sqnorm(phi_ext)
  
  jump <- left - right
  
  return(c(jump, - jump))
}

perform_mll_partial_optimisation <- function(lag_degs, cop_name, Y, X, Delta,
                                             para_fixed, fixed_indices,
                                             init_values_variable,
                                             opt_algo, it_num_constr,
                                             it_num_unconstr,
                                             indep_assumption = FALSE){
  
  current_mllh <- -100000
  current_para_variable <- init_values_variable[[1]]
  
  if (opt_algo == "NM"){
    if (indep_assumption){
      for (init_vals in init_values_variable){
        res <- optim(init_vals[-1], log_lik_indep_partial, method = "Nelder-Mead",
                     control = list(fnscale = -1, maxit = it_num_unconstr),
                     para_fixed = para_fixed, fixed_indices = fixed_indices,
                     lag_degs = lag_degs, cop_name = cop_name,
                     Y = Y, X = X, Delta = Delta)
        new_para_variable <- res[[1]]
        new_mllh <- res[[2]]
        
        if (new_mllh > current_mllh){
          current_mllh <- new_mllh
          current_para_variable <- new_para_variable
        }
      }
    } else {
      for (init_vals in init_values_variable){
        res <- optim(init_vals, log_lik_partial, method = "Nelder-Mead",
                     control = list(fnscale = -1, maxit = it_num_unconstr),
                     para_fixed = para_fixed, fixed_indices = fixed_indices,
                     lag_degs = lag_degs, cop_name = cop_name,
                     Y = Y, X = X, Delta = Delta)
        new_para_variable <- res[[1]]
        new_mllh <- res[[2]]
        
        if (new_mllh > current_mllh){
          current_mllh <- new_mllh
          current_para_variable <- new_para_variable
        }
      }
    }
  }
  
  if (opt_algo == "NMCob"){
    
    opts <- list("algorithm"= "NLOPT_LN_COBYLA", "maxeval"= it_num_constr)
    
    if (indep_assumption){
      for (init_vals in init_values_variable){
        intermed_para_variable <- optim(init_vals[-1], log_lik_indep_partial,
                                        method = "Nelder-Mead",
                                        control = list(fnscale = -1,
                                                       maxit = it_num_unconstr),
                                        para_fixed = para_fixed,
                                        fixed_indices = fixed_indices,
                                        lag_degs = lag_degs,
                                        cop_name = cop_name,
                                        Y = Y, X = X, Delta = Delta)$par
        
        res <- nloptr(x0 = intermed_para_variable,
                      eval_f = neg_log_lik_indep_partial, # max. rather than min.!
                      eval_g_ineq = ctuity_constr_partial,
                      opts = opts,
                      para_fixed = para_fixed, fixed_indices = fixed_indices,
                      lag_degs = lag_degs, cop_name = cop_name,
                      Y = Y, X = X, Delta = Delta)
        new_para_variable <- res$solution
        new_mllh <- - res$objective # Compare with llh rather than neg_llh
        
        if (new_mllh > current_mllh){
          current_mllh <- new_mllh
          current_para_variable <- new_para_variable
        }
      }
    } else {
      for (init_vals in init_values_variable){
        intermed_para_variable <- optim(init_vals, log_lik_partial,
                                        method = "Nelder-Mead",
                                        control = list(fnscale = -1,
                                                       maxit = it_num_unconstr),
                                        para_fixed = para_fixed,
                                        fixed_indices = fixed_indices,
                                        lag_degs = lag_degs,
                                        cop_name = cop_name,
                                        Y = Y, X = X, Delta = Delta)$par
        
        res <- nloptr(x0 = intermed_para_variable,
                      eval_f = neg_log_lik_partial, # max. rather than min.!
                      eval_g_ineq = ctuity_constr_partial,
                      opts = opts,
                      para_fixed = para_fixed, fixed_indices = fixed_indices,
                      lag_degs = lag_degs, cop_name = cop_name,
                      Y = Y, X = X, Delta = Delta)
        new_para_variable <- res$solution
        new_mllh <- - res$objective # Compare with llh rather than neg_llh
        
        if (new_mllh > current_mllh){
          current_mllh <- new_mllh
          current_para_variable <- new_para_variable
        }
      }
    }
  }
  
  # Final step: combine results in one vector
  para_all <- rep(0, length(current_para_variable) + length(para_fixed))
  para_all[fixed_indices] <- para_fixed
  para_all[-fixed_indices] <- current_para_variable
  
  return(list(current_mllh, para_all))
}
###############################################################################


###### Likelihood optimisation under independence assumption ##################

# ktau is present in neither para_variable, nor para_fixed
log_lik_indep_partial <- function(para_variable, para_fixed, fixed_indices,
                                  lag_degs, cop_name, Y, X, Delta){
  all_paras <- rep(0, length(para_variable) + length(para_fixed))
  all_paras[fixed_indices] <- para_fixed
  all_paras[-fixed_indices] <- para_variable
  return(log_lik_fun_indep(all_paras, lag_degs, cop_name, Y, X, Delta))
}

neg_log_lik_indep_partial <- function(para_variable, para_fixed, fixed_indices,
                                      lag_degs, cop_name, Y, X, Delta){
  all_paras <- rep(0, length(para_variable) + length(para_fixed))
  all_paras[fixed_indices] <- para_fixed
  all_paras[-fixed_indices] <- para_variable
  return(-log_lik_fun_indep(all_paras, lag_degs, cop_name, Y, X, Delta))
}


# all_paras_indep = all_paras without eta on first position
log_lik_fun_indep <- function(all_paras_indep, lag_degs, cop_name, Y, X, Delta){
  
  # 1) Retrieving current parameters ----
  paras_T_indices <- c(beta_full_index, gamma_index, lambda_index,
                       phi_til_index(lag_degs), phi_index(lag_degs))
  # no eta present, so no shift + 1
  
  transf_paras_T <- all_paras_indep[paras_T_indices]
  transf_paras_C <- all_paras_indep[-paras_T_indices]
  
  beta_full <- transf_paras_T[beta_full_index]
  transf_lam <- transf_paras_T[lambda_index]
  gam_par <- transf_paras_T[gamma_index]
  phi_til <- transf_paras_T[phi_til_index(lag_degs)]
  phi <- transf_paras_T[phi_index(lag_degs)]
  
  lambda <- lambda_inverse_transform(transf_lam)
  # ----
  
  # 2) Construct argument matrices for censored & uncensored cases ----
  Y_un <- Y[Delta == 1]
  Y_cens <- Y[Delta == 0]
  
  X_un <- X[Delta == 1, ]
  X_cens <- X[Delta == 0, ]
  # ----
  
  # 3) Density & distribution evaluation ----
  
  ## density
  dens_T_un <- dEAL(Y_un, X_un, beta_full, gam_par, lambda, phi_til, phi)
  dens_C_cens <- dCens(Y_cens, X_cens, transf_paras_C)
  
  ## distribution
  distr_T_cens <- pEAL(Y_cens, X_cens, beta_full, gam_par, lambda, phi_til, phi)
  distr_C_un <- pCens(Y_un, X_un, transf_paras_C)
  # ----
  
  lh_uncens <- dens_T_un * (1 - distr_C_un)
  lh_cens <- dens_C_cens * (1 - distr_T_cens)
  
  llh <- sum(log(lh_uncens)) + sum(log(lh_cens))
  
  res <- min(max(llh, -100000), 100000) # avoid returning +- Inf
  if (is.nan(res)){ # avoid NaN (due to Inf - Inf by num. errors) as well
    res <- -100000
  }
  return(res) 
}

neg_log_lik_fun_indep <- function(all_paras_indep, lag_degs, cop_name, Y, X, Delta){
  
  # 1) Retrieving current parameters ----
  paras_T_indices <- c(beta_full_index, gamma_index, lambda_index,
                       phi_til_index(lag_degs), phi_index(lag_degs))
  # no eta present, so no shift + 1
  
  transf_paras_T <- all_paras_indep[paras_T_indices]
  transf_paras_C <- all_paras_indep[-paras_T_indices]
  
  beta_full <- transf_paras_T[beta_full_index]
  transf_lam <- transf_paras_T[lambda_index]
  gam_par <- transf_paras_T[gamma_index]
  phi_til <- transf_paras_T[phi_til_index(lag_degs)]
  phi <- transf_paras_T[phi_index(lag_degs)]
  
  lambda <- lambda_inverse_transform(transf_lam)
  # ----
  
  # 2) Construct argument matrices for censored & uncensored cases ----
  Y_un <- Y[Delta == 1]
  Y_cens <- Y[Delta == 0]
  
  X_un <- X[Delta == 1, ]
  X_cens <- X[Delta == 0, ]
  # ----
  
  # 3) Density & distribution evaluation ----
  
  ## density
  dens_T_un <- dEAL(Y_un, X_un, beta_full, gam_par, lambda, phi_til, phi)
  dens_C_cens <- dCens(Y_cens, X_cens, transf_paras_C)
  
  ## distribution
  distr_T_cens <- pEAL(Y_cens, X_cens, beta_full, gam_par, lambda, phi_til, phi)
  distr_C_un <- pCens(Y_un, X_un, transf_paras_C)
  # ----
  
  lh_uncens <- dens_T_un * (1 - distr_C_un)
  lh_cens <- dens_C_cens * (1 - distr_T_cens)
  
  llh <- sum(log(lh_uncens)) + sum(log(lh_cens))
  
  res <- min(max(llh, -100000), 100000) # avoid returning +- Inf
  if (is.nan(res)){ # avoid NaN (due to Inf - Inf by num. errors) as well
    res <- -100000
  }
  return(-res) 
}

ctuity_constr_fun_indep <- function(all_paras_indep, lag_degs,
                                    cop_name, Y, X, Delta){
  # args. on second line not needed, but should be the same as for obj. fun.
  
  phi_til <- all_paras_indep[phi_til_index(lag_degs)]
  phi <- all_paras_indep[phi_index(lag_degs)]
  
  phi_til_ext <- c(1, phi_til)
  phi_ext <- c(1, phi)
  
  # combination of Lag. polynomials evaluated in 0 on neg./pos. axis:
  left <- sum(phi_til_ext)^2 / sqnorm(phi_til_ext)
  right <- sum(phi_ext)^2 / sqnorm(phi_ext)
  
  jump <- left - right
  
  return(c(jump, - jump))
}

###############################################################################



########## Degree selection (AIC-based) #######################################
deg_sel_AIC_grid_only_T <- function(cop_name, Y, X, Delta,
                                        T1, X1, C0, X0,
                                        indep_assumption = FALSE,
                                        max_deg = lag_deg_upper){
  
  ### External printing ###
  AIC_grid_file <- paste0(folder_path, "/AIC_intermediate_grids.txt")
  write(paste0("Simulation index: ", simulation_index),
        file = AIC_grid_file, append = TRUE)
  write("\n", file = AIC_grid_file, append = TRUE)
  
  BIC_grid_file <- paste0(folder_path, "/BIC_intermediate_grids.txt")
  write(paste0("Simulation index: ", simulation_index),
        file = BIC_grid_file, append = TRUE)
  write("\n", file = BIC_grid_file, append = TRUE)
  #########################
  
  
  # 1. first perform optimisation under zero degrees (using Nelder-Mead)
  init_val_basis <- determine_init_basis(T1,X1,C0,X0,Delta)
  mll_basis <- perform_mll_optimisation(c(0,0), test_cop_name,
                                        Y, X, Delta,
                                        init_val_list = init_val_basis,
                                        opt_algo = "NM",
                                        it_num_constr = 0,
                                        it_num_unconstr = it_NM,
                                        indep_assumption = indep_assumption)
  para_basis <- mll_basis[[2]]
  
  # print("Estimate for zero degrees:")
  # print(as.vector(round(para_inv_transform(para_basis, cop_name), DigNum)))
  
  ### Benchmark: AIC/BIC score for mll optimisation under degrees (0,0)
  basis_para_num <- length(para_basis)
  BIC_factor <- log(sample_size)
  basis_AIC <- 2*basis_para_num - 2* mll_basis[[1]]
  basis_BIC <- BIC_factor*basis_para_num - 2* mll_basis[[1]]
  
  
  
  
  T_indices <- ktau_length_test + c(beta_full_index, gamma_index, lambda_index)
  para_T_basis <- para_basis[T_indices]
  para_fixed_basis <- para_basis[-T_indices]
  
  
  
  ### AIC/BIC degree selection
  # AIC
  all_AIC_scores <- matrix(rep(0, (max_deg + 1)^2),
                           nrow = (max_deg + 1), byrow = TRUE)
  all_AIC_scores[1,1] <- basis_AIC
  
  best_AIC_degrees <- c(0,0)
  best_AIC_score <- basis_AIC
  best_AIC_transf_paras <- para_basis
  
  # BIC
  all_BIC_scores <- matrix(rep(0, (max_deg + 1)^2),
                           nrow = (max_deg + 1), byrow = TRUE)
  all_BIC_scores[1,1] <- basis_BIC
  
  best_BIC_degrees <- c(0,0)
  best_BIC_score <- basis_BIC
  best_BIC_transf_paras <- para_basis
  
  # 2. Then perform optimisation under range of degrees (grid approach)
  for (L_degree in (seq_len(max_deg + 1) - 1)){ 
    for (R_degree in (seq_len(max_deg + 1) - 1)){
      if (L_degree + R_degree > 0){
        # print(paste0("Now testing: (L, R) degree: ",
        #              toString(c(L_degree, R_degree))))
        
        
        
        ## determine initial values
        total_degree <- L_degree + R_degree
        # fix everything except the indices for T (new phis also not fixed)
        fixed_indices <- seq_len(
          length(para_basis) + total_degree
        )[-c(T_indices, max(T_indices) + seq_len(total_degree))]
        
        init_val_variable <- vector(mode = "list",
                                    length = init_value_number_intermed)
        for (j in 1:init_value_number_intermed){
          set.seed((total_degree + 1)*(init_seeds[3] + j))
          random_phis <- runif(total_degree,
                               lower_bound_on_phis, upper_bound_on_phis)
          
          if (ktau_length_test == 1){
            init_val_variable[[j]] <- c(
              slight_perturb(para_T_basis, (total_degree + 1)*(init_seeds[3] + j)),
              random_phis)
          } else {
            init_val_variable[[j]] <- c(0,
                                        slight_perturb(para_T_basis, (total_degree + 1)*(init_seeds[3] + j)),
                                        random_phis)
          }
        }
        
        new_mll <- perform_mll_partial_optimisation(
          lag_degs = c(L_degree, R_degree),
          cop_name = cop_name,
          Y = Y, X = X, Delta = Delta,
          para_fixed = para_fixed_basis,
          fixed_indices = fixed_indices,
          init_values_variable = init_val_variable,
          opt_algo = "NMCob",
          it_num_constr = it_NMCob_constr,
          it_num_unconstr = it_NMCob_unconstr,
          indep_assumption = indep_assumption)
        
        new_AIC <- 2*(basis_para_num + total_degree) - 2* new_mll[[1]]
        new_BIC <- BIC_factor*(basis_para_num + total_degree) - 2* new_mll[[1]]
        
        # storing result in grid
        all_AIC_scores[L_degree + 1, R_degree + 1] <- new_AIC
        all_BIC_scores[L_degree + 1, R_degree + 1] <- new_BIC
        
        ## update minimum
        if (new_AIC < best_AIC_score){
          best_AIC_degrees <- c(L_degree, R_degree)
          best_AIC_score <- new_AIC
          best_AIC_transf_paras <- new_mll[[2]]
        }
        if (new_BIC < best_BIC_score){
          best_BIC_degrees <- c(L_degree, R_degree)
          best_BIC_score <- new_BIC
          best_BIC_transf_paras <- new_mll[[2]]
        }
      }
    }
  }
  
  # print(paste0("Selected AIC degrees: ", toString(best_AIC_degrees)))
  # print(as.vector(round(best_AIC_transf_paras, DigNum)))
  # 
  # print(paste0("Selected BIC degrees: ", toString(best_BIC_degrees)))
  # print(as.vector(round(best_BIC_transf_paras, DigNum)))
  
  
  
  ## External printing ##################
  Ldeg_names <- paste(rep("m_til =", max_deg + 1),(0:max_deg))
  Rdeg_names <- paste(rep("m =", max_deg + 1),(0:max_deg))
  
  # AIC
  df_AIC_scores <- as.data.frame(all_AIC_scores)
  rownames(df_AIC_scores) <- Ldeg_names
  colnames(df_AIC_scores) <- Rdeg_names
  
  print.char.matrix(df_AIC_scores, file = AIC_grid_file, cell.align = "cen",
                    col.names = TRUE, append = TRUE,
                    hsep = " ", vsep = "", csep = "")
  write("\n", file = AIC_grid_file, append = TRUE)
  
  write(paste0("Selected degrees: ", toString(best_AIC_degrees)),
        file = AIC_grid_file, append = TRUE)
  write("-----", file = AIC_grid_file, append = TRUE)
  
  
  #BIC
  df_BIC_scores <- as.data.frame(all_BIC_scores)
  rownames(df_BIC_scores) <- Ldeg_names
  colnames(df_BIC_scores) <- Rdeg_names
  
  print.char.matrix(df_BIC_scores, file = BIC_grid_file, cell.align = "cen",
                    col.names = TRUE, append = TRUE,
                    hsep = " ", vsep = "", csep = "")
  write("\n", file = BIC_grid_file, append = TRUE)
  
  write(paste0("Selected degrees: ", toString(best_BIC_degrees)),
        file = BIC_grid_file, append = TRUE)
  write("-----", file = BIC_grid_file, append = TRUE)
  #######################################################
  
  
  return(list(best_AIC_degrees, best_AIC_transf_paras))
}
###############################################################################


########## Get performance & print (settings & results) externally ############
# returns mean, RMSE, standard deviation and bias matrices
get_qu_performance <- function(){
  qu_means_matrix <- matrix(rep(0, length(quantile_levels)* X_selection_size),
                            nrow = length(quantile_levels), byrow = TRUE)
  
  qu_RMSE_matrix <- matrix(rep(0, length(quantile_levels)* X_selection_size),
                           nrow = length(quantile_levels), byrow = TRUE)
  
  qu_bias_matrix <- matrix(rep(0, length(quantile_levels)* X_selection_size),
                           nrow = length(quantile_levels), byrow = TRUE)
  
  qu_biasrel_matrix <- matrix(rep(0, length(quantile_levels)* X_selection_size),
                              nrow = length(quantile_levels), byrow = TRUE)
  
  qu_var_matrix <- matrix(rep(0, length(quantile_levels)* X_selection_size),
                          nrow = length(quantile_levels), byrow = TRUE)
  
  
  # mean, RMSE & bias
  for (qu_index in seq_along(quantile_levels)){
    sel_qu_estimates <- sel_qu_estimates_list[[qu_index]]
    sel_qu_true_values <- sel_qu_true_values_matrix[qu_index, ]
    
    qu_means_matrix[qu_index, ] <- colMeans(sel_qu_estimates)
    qu_RMSE_matrix[qu_index, ] <- sqrt(colMeans((sweep(sel_qu_estimates, 2,
                                                       sel_qu_true_values))^2))
    # "sweep": subtract true quantiles from each row in the matrix of estimates
    absolute_bias <- colMeans(sweep(sel_qu_estimates, 2,
                                    sel_qu_true_values))
    qu_bias_matrix[qu_index, ] <- absolute_bias
    
    # relative bias
    qu_biasrel_matrix[qu_index, ] <- absolute_bias / sel_qu_true_values
  }
  
  # variance
  for (qu_index in seq_along(quantile_levels)){
    sel_qu_estimates <- sel_qu_estimates_list[[qu_index]]
    sel_qu_mean_estimates <- qu_means_matrix[qu_index, ]
    
    qu_var_matrix[qu_index, ] <- colMeans((sweep(sel_qu_estimates, 2,
                                                 sel_qu_mean_estimates))^2)
  }
  
  return(list(qu_means_matrix, qu_RMSE_matrix, qu_var_matrix, qu_bias_matrix,
              qu_biasrel_matrix))
}

print_qu_performance_summary <- function(){
  
  qu_summary_file <-  paste0(folder_path, "/quantile_summary.txt")
  
  for (qu_index in seq_along(quantile_levels)){
    
    this_quantile <- paste0(toString(quantile_levels[qu_index]), "-th qu")
    
    # storing all quantile predictions in the selection 
    est_qu_sel_file <- paste0(folder_path, "/est_qu_sel_",
                              this_quantile, ".txt")
    
    print.char.matrix(as.data.frame(
      round(sel_qu_estimates_list[[qu_index]], digits = DigNum)),
      file = est_qu_sel_file,
      cell.align = "cen", col.txt.align = "cen", 
      col.names = FALSE, row.names = TRUE, 
      hsep = "  ", vsep = "", csep = "", append = TRUE)
    
    # storing performance summary
    sel_qu_true_short <- round(sel_qu_true_values_matrix[qu_index,],
                               digits = DigNum)
    sel_qu_mean_short <- round(sel_qu_means[qu_index, ], digits = DigNum)
    sel_qu_RMSE_short <- round(sel_qu_RMSE[qu_index, ], digits = DigNum)
    sel_qu_var_short <- round(sel_qu_var[qu_index, ], digits = DigNum)
    sel_qu_bias_short <- round(sel_qu_bias[qu_index, ], digits = DigNum)
    sel_qu_biasrel_short <- round(sel_qu_biasrel[qu_index, ], digits = DigNum)
    
    df_qu_sum_this_level <- as.data.frame(
      rbind(sel_qu_true_short, sel_qu_mean_short, sel_qu_var_short,
            sel_qu_RMSE_short, sel_qu_bias_short, sel_qu_biasrel_short),
      row.names = c(paste0("True ", this_quantile),
                    paste0("Mean est ", this_quantile),
                    paste0("Variance ", this_quantile),
                    paste0("RMSE ", this_quantile),
                    paste0("Bias ", this_quantile),
                    paste0("Bias (rel) ", this_quantile)))
    
    write("\n", file = qu_summary_file, append = TRUE)
    print.char.matrix(df_qu_sum_this_level, file = qu_summary_file,
                      cell.align = "cen", col.txt.align = "cen", 
                      col.names = TRUE, row.names = TRUE, 
                      hsep = " ", vsep = "", csep = "", append = TRUE)
  }
}

para_performance_summary <- function(ext_print = FALSE,
                                           ext_boxplots = FALSE){
  
  ####### Valid in general ######################
  alpha_C_all <- rep("alpha_C", X_dimension)
  beta_T_all <- rep("beta_T", X_dimension)
  gam_all <- rep("gamma", X_dimension)
  
  for (j in seq_len(X_dimension)){
    alpha_C_all[j] <- paste0(alpha_C_all[j], toString(j))
    beta_T_all[j] <- paste0(beta_T_all[j], toString(j))
    gam_all[j] <- paste0(gam_all[j], toString(j))
  }
  
  
  sel_deg_matrix <- cbind(sel_deg_left, sel_deg_right)
  # matrix with first column the selected tilde(m), second m.
  
  max_left_degree <- max(sel_deg_left)
  max_right_degree <- max(sel_deg_right)
  
  ###############################################
  
  if (true_distr_T == "EAL"){
    # in this case, both lambda and (possibly) phi's are present in true para
    true_left_deg <- true_lag_degrees[1]
    true_right_deg <- true_lag_degrees[2]
    
    max_overall_left_deg <- max(true_left_deg, max_left_degree)
    max_overall_right_deg <- max(true_right_deg, max_right_degree)
    
    
    
    
    ## preparing the names ##
    phi_til_all <- rep("", max_overall_left_deg)
    
    for (j in seq_len(max_overall_left_deg)){
      phi_til_all[j] <- paste0("phi_til", toString(j))
    }
    
    phi_all <- rep("", max_overall_right_deg)
    
    for (j in seq_len(max_overall_right_deg)){
      phi_all[j] <- paste0("phi", toString(j))
    }
    
    para_names_adjusted <- c("ktau", "beta_0", beta_T_all, "gamma_0",gam_all,
                             "lambda", phi_til_all, phi_all,
                             "alpha_0", alpha_C_all, "sigma_C")
    
    
    
    
    ## now adjust the length of both the true para and the estimates ##
    
    # put "-" at the place of any parameter not present in the true vector
    true_paras_short_adj <- round(true_paras, DigNum)
    
    true_diff_left <- max_overall_left_deg - true_left_deg
    true_diff_right <- max_overall_right_deg - true_right_deg
    
    non_present_indices <- c()
    
    if (true_diff_left > 0){
      
      if (true_left_deg == 0){
        append_index <- lambda_index + ktau_length_true
      } else {
        append_index <- max(phi_til_index(true_lag_degrees)) + ktau_length_true
      }
      
      true_paras_short_adj <- append(true_paras_short_adj,
                                     rep("-", true_diff_left),
                                     after = append_index)
      non_present_indices <- c(non_present_indices,
                               append_index + seq_len(true_diff_left))
    }
    
    if (true_diff_right > 0){
      
      if (true_right_deg == 0){
        append_index <- lambda_index + max_overall_left_deg + ktau_length_true
      } else {
        append_index <- max(phi_index(
          lag_degs = c(max_overall_left_deg, true_right_deg))) +
          ktau_length_true
      }
      
      true_paras_short_adj <- append(true_paras_short_adj,
                                     rep("-", true_diff_right),
                                     after = append_index)
      non_present_indices <- c(non_present_indices,
                               append_index + seq_len(true_diff_right))
    }
    
    # put "-" similarly for the para estimates, and also make a version with
    # zeros added, for the computation of means etc.
    
    # + 1 for ktau (put 0 or '-' anyway, even if not present in true/test)
    max_para_num <- 3*X_dimension + 5 + 1 +
      max_overall_left_deg + max_overall_right_deg
    para_estimates_matrix_zero_fill <- matrix(rep(0, max_para_num*
                                                    simulation_size),
                                              ncol = max_para_num)
    para_estimates_matrix_empty_fill <- matrix(rep(0, max_para_num*
                                                     simulation_size),
                                               ncol = max_para_num)
    
    for (sim_ind in seq_len(simulation_size)){
      sel_left_deg <- as.numeric(sel_deg_matrix[sim_ind, 1])
      sel_right_deg <- as.numeric(sel_deg_matrix[sim_ind, 2])
      
      sel_diff_left <- max_overall_left_deg - sel_left_deg
      sel_diff_right <- max_overall_right_deg - sel_right_deg
      
      sel_paras_zeros_adj <- all_para_estimates[[sim_ind]]
      sel_paras_short_adj <- round(all_para_estimates[[sim_ind]], DigNum)
      
      
      if (sel_diff_left > 0){
        
        if (sel_left_deg == 0){
          append_index <- lambda_index + ktau_length_test
        } else {
          append_index <- max(phi_til_index(
            lag_degs = c(sel_left_deg, sel_right_deg))) + ktau_length_test
        }
        
        sel_paras_short_adj <- append(sel_paras_short_adj,
                                      rep("-", sel_diff_left),
                                      after = append_index)
        sel_paras_zeros_adj <- append(sel_paras_zeros_adj,
                                      rep(0, sel_diff_left),
                                      after = append_index)
      }
      
      if (sel_diff_right > 0){
        
        if (sel_right_deg == 0){
          append_index <- lambda_index + max_overall_left_deg  +
            ktau_length_test
        } else {
          append_index <- max(phi_index(
            lag_degs = c(max_overall_left_deg, sel_right_deg))) +
            ktau_length_test
        }
        
        
        sel_paras_short_adj <- append(sel_paras_short_adj,
                                      rep("-", sel_diff_right),
                                      after = append_index)
        sel_paras_zeros_adj <- append(sel_paras_zeros_adj,
                                      rep(0, sel_diff_right),
                                      after = append_index)
      }
      
      if (ktau_length_test == 0){
        # true (indep) parameters contain 0 for ktau, so adjust test one with "-"
        sel_paras_short_adj <- c("-", sel_paras_short_adj)
        sel_paras_zeros_adj <- c(0, sel_paras_zeros_adj)
      }
      
      para_estimates_matrix_empty_fill[sim_ind,] <- sel_paras_short_adj
      para_estimates_matrix_zero_fill[sim_ind,] <- sel_paras_zeros_adj
    }
    
    
    
    ### For parameter estimates ###
    mean_para_estimates <- colMeans(para_estimates_matrix_zero_fill)
    var_para_estimates <- colMeans((sweep(para_estimates_matrix_zero_fill,
                                          2, mean_para_estimates))^2)
    
    if (ktau_length_test == 1){
      mean_short <- round(mean_para_estimates, digits = DigNum)
      var_short <- round(var_para_estimates, digits = DigNum)
    } else { # replace 0 by "-", since ktau not present in the testing
      mean_short <- c("-", round(mean_para_estimates[-1], digits = DigNum))
      var_short <- c("-", round(var_para_estimates[-1], digits = DigNum))
    }
    
    
    
    bias_short <- rep(0, max_para_num)
    biasrel_short <- rep(0, max_para_num)
    RMSE_short <- rep(0, max_para_num)
    
    if (length(non_present_indices) > 0){
      # compute RMSE before bias is turned into string instead of numeric
      bias_short[-non_present_indices] <- round(
        mean_para_estimates[-non_present_indices] - true_paras, digits = DigNum)
      biasrel_short[-non_present_indices] <- round(
        (mean_para_estimates[-non_present_indices] - true_paras)/true_paras,
        digits = DigNum)
      RMSE_short[-non_present_indices] <- round(
        sqrt(var_para_estimates[-non_present_indices] +
               bias_short[-non_present_indices]^2), digits = DigNum)
      
      bias_short[non_present_indices] <- rep("-", length(non_present_indices))
      biasrel_short[non_present_indices] <- rep("-", length(non_present_indices))
      RMSE_short[non_present_indices] <- rep("-", length(non_present_indices))
    } else {
      # compute RMSE before bias is turned into string instead of numeric
      bias_short <- round(
        mean_para_estimates - true_paras, digits = DigNum)
      biasrel_short <- round(
        (mean_para_estimates - true_paras)/true_paras, digits = DigNum)
      RMSE_short <- round(
        sqrt(var_para_estimates +
               bias_short^2), digits = DigNum)
    }
    
    
    if (ktau_length_test == 0){
      bias_short <- c("-", bias_short[-1])
      biasrel_short <- c("-", biasrel_short[-1])
      RMSE_short <- c("-", RMSE_short[-1])
    }
    
  } else { # This assumes true_paras consists of
    # ktau, beta, gamma and part for C only, no other parameters for T!
    
    ## preparing the names ##
    phi_til_all <- rep("", max_left_degree)
    
    for (j in seq_len(max_left_degree)){
      phi_til_all[j] <- paste0("phi_til", toString(j))
    }
    
    phi_all <- rep("", max_right_degree)
    
    for (j in seq_len(max_right_degree)){
      phi_all[j] <- paste0("phi", toString(j))
    }
    
    para_names_adjusted <- c("ktau", "beta_0", beta_T_all, "gamma_0",gam_all,
                             "lambda", phi_til_all, phi_all,
                             "alpha_0", alpha_C_all, "sigma_C")
    
    
    
    
    ## now adjust the length of both the true para and the estimates ##
    
    # put "-" at the place of lambda and phis
    true_paras_short_adj <- append(round(true_paras, DigNum),
                                   rep("-", max_left_degree +
                                         max_right_degree + 1),
                                   after = max(gamma_index) + ktau_length_true)
    non_present_indices <- max(gamma_index) + ktau_length_true +
      seq_len(max_left_degree + max_right_degree + 1)
    
    
    
    # put "-" similarly for the para estimates, and also make a version with
    # zeros added, for the computation of means etc.
    
    # + 1 for ktau (put 0 or '-' anyway, even if not present in true/test)
    max_para_num <- 3*X_dimension + 5 + 1 +
      max_left_degree + max_right_degree
    para_estimates_matrix_zero_fill <- matrix(rep(0, max_para_num*
                                                    simulation_size),
                                              ncol = max_para_num)
    para_estimates_matrix_empty_fill <- matrix(rep(0, max_para_num*
                                                     simulation_size),
                                               ncol = max_para_num)
    
    for (sim_ind in seq_len(simulation_size)){
      sel_left_deg <- as.numeric(sel_deg_matrix[sim_ind, 1])
      sel_right_deg <- as.numeric(sel_deg_matrix[sim_ind, 2])
      
      sel_diff_left <- max_left_degree - sel_left_deg
      sel_diff_right <- max_right_degree - sel_right_deg
      
      sel_paras_zeros_adj <- all_para_estimates[[sim_ind]]
      sel_paras_short_adj <- round(all_para_estimates[[sim_ind]], DigNum)
      
      
      if (sel_diff_left > 0){
        
        if (sel_left_deg == 0){
          append_index <- lambda_index + ktau_length_test
        } else {
          append_index <- max(phi_til_index(
            lag_degs = c(sel_left_deg, sel_right_deg))) + ktau_length_test
        }
        
        sel_paras_short_adj <- append(sel_paras_short_adj,
                                      rep("-", sel_diff_left),
                                      after = append_index)
        sel_paras_zeros_adj <- append(sel_paras_zeros_adj,
                                      rep(0, sel_diff_left),
                                      after = append_index)
      }
      
      if (sel_diff_right > 0){
        
        if (sel_right_deg == 0){
          append_index <- lambda_index + max_left_degree  + ktau_length_test
        } else {
          append_index <- max(phi_index(
            lag_degs = c(max_left_degree, sel_right_deg))) + ktau_length_test
        }
        
        
        sel_paras_short_adj <- append(sel_paras_short_adj,
                                      rep("-", sel_diff_right),
                                      after = append_index)
        sel_paras_zeros_adj <- append(sel_paras_zeros_adj,
                                      rep(0, sel_diff_right),
                                      after = append_index)
      }
      
      
      if (ktau_length_test == 0){
        # true (indep) parameters contain 0 for ktau, so adjust test one with "-"
        sel_paras_short_adj <- c("-", sel_paras_short_adj)
        sel_paras_zeros_adj <- c(0, sel_paras_zeros_adj)
      }
      
      para_estimates_matrix_empty_fill[sim_ind,] <- sel_paras_short_adj
      para_estimates_matrix_zero_fill[sim_ind,] <- sel_paras_zeros_adj
    }
    
    
    ### For parameter estimates ###
    mean_para_estimates <- colMeans(para_estimates_matrix_zero_fill)
    var_para_estimates <- colMeans((sweep(para_estimates_matrix_zero_fill,
                                          2, mean_para_estimates))^2)
    
    if (ktau_length_test == 1){
      mean_short <- round(mean_para_estimates, digits = DigNum)
      var_short <- round(var_para_estimates, digits = DigNum)
    } else { # replace 0 by "-", since ktau not present in the testing
      mean_short <- c("-", round(mean_para_estimates[-1], digits = DigNum))
      var_short <- c("-", round(var_para_estimates[-1], digits = DigNum))
    }
    
    bias_short <- rep(0, max_para_num)
    biasrel_short <- rep(0, max_para_num)
    RMSE_short <- rep(0, max_para_num)
    
    # compute RMSE before bias is turned into string instead of numeric
    bias_short[-non_present_indices] <- round(
      mean_para_estimates[-non_present_indices] - true_paras, digits = DigNum)
    biasrel_short[-non_present_indices] <- round(
      (mean_para_estimates[-non_present_indices] - true_paras)/true_paras,
      digits = DigNum)
    RMSE_short[-non_present_indices] <- round(
      sqrt(var_para_estimates[-non_present_indices] +
             bias_short[-non_present_indices]^2), digits = DigNum)
    
    bias_short[non_present_indices] <- rep("-", length(non_present_indices))
    biasrel_short[non_present_indices] <- rep("-", length(non_present_indices))
    RMSE_short[non_present_indices] <- rep("-", length(non_present_indices))
    
    if (ktau_length_test == 0){
      bias_short <- c("-", bias_short[-1])
      biasrel_short <- c("-", biasrel_short[-1])
      RMSE_short <- c("-", RMSE_short[-1])
    }
  }
  
  
  
  
  ### External printing part ###
  if (ext_print){
    ## overview of parameter summary statistics ##
    df_parameters <- as.data.frame(
      rbind(true_paras_short_adj, mean_short, var_short,
            RMSE_short, bias_short, biasrel_short),
      row.names = c("True parameters", "Mean estimates", "Variance",
                    "RMSE", "Bias", "Bias (rel)"))
    colnames(df_parameters) <- para_names_adjusted
    
    para_summary_file <-  paste0(folder_path,"/para_summary.txt")
    print.char.matrix(df_parameters, file = para_summary_file,
                      cell.align = "cen",
                      col.names = TRUE, row.names = TRUE, append = TRUE,
                      hsep = " ", vsep = "", csep = "")
    
    ## all parameter estimates, per sample ##
    df_all_para_estimates <-as.data.frame(para_estimates_matrix_empty_fill)
    colnames(df_all_para_estimates) <- para_names_adjusted
    
    para_est_file <- paste0(folder_path, "/para_estimates.txt")
    print.char.matrix(df_all_para_estimates, file = para_est_file,
                      cell.align = "cen", col.txt.align = "cen", 
                      col.names = TRUE, row.names = TRUE, append = TRUE,
                      hsep = " ", vsep = "", csep = "")
  }
  
  if (ext_boxplots){
    # Boxplots only for (ktau), beta, gamma and lambda, present everywhere
    reduced_para_est_mat <- matrix(rep(0, simulation_size*(ktau_length_test +
                                                             lambda_index)),
                                   nrow = simulation_size, byrow = TRUE)
    for (k in seq_len(simulation_size)){
      reduced_para_est_mat[k,] <- all_para_estimates[[k]][
        seq_len(ktau_length_test + lambda_index)]
    }
    
    
    for (j in seq_len(ktau_length_test + lambda_index)){
      png(file=paste0(folder_path, "/Boxplots/Boxplot_",
                      para_names_adjusted[j],".png",sep=""))
      boxplot(reduced_para_est_mat[,j], horizontal = TRUE,
              main = paste0("Estimates for ", para_names_adjusted[j]))
      dev.off()
    }
  }
  
  
  ### Return basic summary statistics
  return(list(mean_short, RMSE_short, var_short, bias_short, biasrel_short))
}


# to print extra information (e.g. settings, # uncens. obs., ...)
external_print_fun <- function(){
  ### preparing the file names ###
  settings_file <- paste0(folder_path, "/all_settings.txt")
  covar_sel_file <- paste0(folder_path, "/covar_sel.txt")
  true_qu_sel_file <- paste0(folder_path, "/true_qu_selection.txt")
  llh_file <- paste0(folder_path, "/mll_llh_values.txt")
  sel_deg_file <- paste0(folder_path, "/selected_degrees.txt")
  data_summary_file <- paste0(folder_path, "/data_summary.txt")
  
  ### gather & print results in data frames ###
  
  if (X_distribution == "norm"){
    X_setting <- paste(toString(X_mean), toString(X_var), sep = ", ")
    X_setting_name <- "Covariate (norm.) mean, variance"
  }
  if (X_distribution == "unif"){
    X_setting <- paste(toString(X_lower), toString(X_upper), sep = ", ")
    X_setting_name <- "Covariate (unif.) lower,upper"
  }
  
  all_setting_names <- c("Simulation size", "Sample size",
                         "# iterations NMCob (unconstrained)",
                         "# iterations NMCob (constrained)",
                         "# iterations NM",
                         "Init. value lower bound", "Init. value upper bound",
                         "-----",
                         "True copula", "True distribution T",
                         "Parameters true distr. T",
                         X_setting_name,
                         "Test copula",
                         "----",
                         "basic_seed",
                         "---",
                         "Total runtime (sec.)", "Uncensoring rate",
                         "--",
                         "init_value_number_basis",
                         "init_value_number_intermed",
                         "init_value_number_final")
  
  all_setting_values <- c(simulation_size, sample_size,
                          it_NMCob_unconstr, it_NMCob_constr, it_NM,
                          lower_bound_on_phis, upper_bound_on_phis,
                          "-----",
                          true_cop_name, true_distr_T,
                          toString(true_paras_T_reduced_string),
                          X_setting,
                          test_cop_name,
                          "----",
                          basic_seed,
                          "---",
                          runtime,
                          round((sum(all_uncens_obs_numbers))/
                                  (sample_size*simulation_size), DigNum),
                          "--",
                          init_value_number_basis,
                          init_value_number_intermed,
                          init_value_number_final)
  
  df_settings <- as.data.frame(all_setting_values,
                               row.names = all_setting_names)
  
  print.char.matrix(df_settings, file = settings_file, cell.align = "cen",
                    row.names = TRUE, append = TRUE,
                    hsep = " ", vsep = "", csep = "")
  
  
  # summary of the data: # uncens. obs., mean, variance, censoring rate
  summary_T_on_X <- round(c(mean(means_T_on_X), mean(variances_T_on_X)), DigNum)
  summary_C_on_X <- round(c(mean(means_C_on_X), mean(variances_C_on_X)), DigNum)
  uncensoring_rate <- round((sum(all_uncens_obs_numbers))/
                              (sample_size*simulation_size), DigNum)
  
  
  df_data_summary <- as.data.frame(cbind(summary_T_on_X, summary_C_on_X))
  rownames(df_data_summary) <- c("mean of means", "mean of variances")
  colnames(df_data_summary) <- c("T|X", "C|X")
  
  df_uncens_obs <- as.data.frame(all_uncens_obs_numbers)
  colnames(df_uncens_obs) <- paste0("# uncens. obs. (out of ", sample_size, ")")
  
  
  write(paste0("uncensoring rate = ", uncensoring_rate),
        file = data_summary_file, append = TRUE)
  write("\n", file = data_summary_file, append = TRUE)
  print.char.matrix(df_data_summary, file = data_summary_file,
                    cell.align = "cen", col.txt.align = "cen",
                    col.names = TRUE, row.names = TRUE, append = TRUE,
                    hsep = " ", vsep = "", csep = "")
  write("\n", file = data_summary_file, append = TRUE)
  print.char.matrix(df_uncens_obs, file = data_summary_file,
                    cell.align = "cen", col.txt.align = "cen",
                    col.names = TRUE, row.names = TRUE, append = TRUE,
                    hsep = " ", vsep = "", csep = "")
  
  
  
  # Covariate selection
  print.char.matrix(as.data.frame(round(X_selection, DigNum)),
                    file = covar_sel_file,
                    cell.align = "cen", col.txt.align = "cen", 
                    col.names = FALSE, row.names = TRUE, append = TRUE,
                    hsep = " ", vsep = "", csep = "")
  
  # True quantile values in covariate selection
  print.char.matrix(as.data.frame(round(sel_qu_true_values_matrix, DigNum)),
                    file = true_qu_sel_file,
                    cell.align = "cen", col.txt.align = "cen", 
                    col.names = FALSE, row.names = TRUE, append = TRUE,
                    hsep = " ", vsep = "", csep = "")
  
  # Estimated mll for each sample (+ llh true parameters if EAL generated)
  if (true_distr_T == "EAL"){
    df_all_llh <- as.data.frame(round(
      cbind(all_mll_estimates, all_llh_true_values), DigNum))
    colnames(df_all_llh) <- c("mll estimate", "llh (true para)")
  } else {
    df_all_llh <- as.data.frame(round(cbind(all_mll_estimates), DigNum))
    colnames(df_all_llh) <- c("mll estimate")
  }
  print.char.matrix(df_all_llh, file = llh_file,
                    cell.align = "cen", col.txt.align = "cen", 
                    col.names = TRUE, row.names = TRUE, append = TRUE,
                    hsep = " ", vsep = "", csep = "")
  
  # selected degrees using AIC
  df_sel_deg <- as.data.frame(cbind(sel_deg_left, sel_deg_right))
  colnames(df_sel_deg) <- c("deg left", "deg right")
  
  print.char.matrix(df_sel_deg, file = sel_deg_file,
                    cell.align = "cen", col.txt.align = "cen", 
                    col.names = TRUE, row.names = TRUE, append = TRUE,
                    hsep = " ", vsep = "", csep = "")
}
###############################################################################

############ PART 1: END ######################################################





############ PART 2: PREPARATION ##############################################

## random seed generation ##############################################
if (basic_seed == FALSE){
  basic_seed <- as.integer(Sys.time())
}

# additional seeds, determined by basic_seed (s.t. only one needs to be
# supplied to verify previous results); random operations to bring variation
set.seed(basic_seed %% 100000)
covariate_seeds <- sample(1:123456, simulation_size, replace = FALSE)

set.seed(abs((basic_seed %% 100)^2 - 5*(basic_seed %% 100)) %% 100000)
copula_seeds <- sample(1:123456, simulation_size, replace = FALSE)

set.seed((basic_seed^2) %% 1000)
init_seeds <- sample(1:123456, 8, replace = FALSE)
########################################################################

## Convert input to appropriate forms for the functions to be applied ####
if (test_cop_name == "indep"){
  ktau_length_test <- 0
  indep_assumption <- TRUE
} else {
  ktau_length_test <- 1
  indep_assumption <- FALSE
}
ktau_length_true <- as.numeric(!(true_cop_name == "indep"))

true_eta <- ktau_to_eta(ktau = true_ktau, cop_name = true_cop_name)
true_theta <- ktau_to_theta(ktau = true_ktau, cop_name = true_cop_name)
true_beta_full <- c(true_beta_0, true_beta_T)
true_log_sigma_C <- log(true_sigma_C)
true_transf_paras_C <- c(true_alpha_0, true_alpha_C, true_log_sigma_C)
true_paras_C <- c(true_alpha_0, true_alpha_C, true_sigma_C)


if (true_distr_T == "EAL"){
  true_paras_T <- c(true_beta_0, true_beta_T, true_gam_par,
                    true_lambda, true_phi_til, true_phi)
  true_transf_lam <- lambda_transform(true_lambda)
  true_transf_paras_T <- c(true_beta_0, true_beta_T, true_gam_par,
                           true_transf_lam, true_phi_til, true_phi)
  true_lag_degrees <- c(length(true_phi_til), length(true_phi))
  true_paras_T_reduced_string <- paste0("lam = ", toString(true_lambda),
                                        " phi_til = ", toString(true_phi_til),
                                        " phi = ", toString(true_phi))
}

if (true_distr_T == "norm"){
  true_paras_T <- c(true_beta_0, true_beta_T, true_gam_par)
  true_transf_paras_T <- c(true_beta_0, true_beta_T, true_gam_par)
  true_paras_T_reduced_string <- ""
}

if (true_distr_T == "exp"){
  true_paras_T <- c(true_beta_0, true_beta_T, true_gam_par)
  true_transf_paras_T <- c(true_beta_0, true_beta_T, true_gam_par)
  true_paras_T_reduced_string <- ""
}

true_transf_paras <- c(true_eta, true_transf_paras_T, true_transf_paras_C)
true_paras <- c(true_ktau, true_paras_T, true_paras_C)
true_para_num <- length(true_paras)
########################################################################

## Parameter positions & true distribution #############################
## indices where parameters can be found (in paras_T; in general vector: shift
# by ktau_length (0 or 1) for eta/ktau)
beta_full_index <- 1:(X_dimension + 1)
gamma_index <- (X_dimension + 2) : (2*X_dimension + 2)
lambda_index <- c(2*X_dimension + 3)

phi_til_index <- function(lag_degs){
  if (lag_degs[1] == 0){
    return(c())
  } else {
    return((2*X_dimension + 4):(2*X_dimension + 3 + lag_degs[1])) 
  }
}
phi_index <- function(lag_degs){
  if (lag_degs[2] == 0){
    return(c())
  } else {
    return((2*X_dimension + 4 + lag_degs[1]):
             (2*X_dimension + 3 + lag_degs[1] + lag_degs[2]))
  }
}

if (true_distr_T == "EAL"){
  # transf_paras_T = c(beta_0, beta_T, gam_par, transf_lam, phi_til, phi)
  
  dSurv <- function(y,x, transf_paras_T){
    beta <- transf_paras_T[beta_full_index]
    gam_par <- transf_paras_T[gamma_index]
    lambda <- lambda_inverse_transform(transf_paras_T[lambda_index])
    phi_til = transf_paras_T[phi_til_index(true_lag_degrees)]
    phi = transf_paras_T[phi_index(true_lag_degrees)]
    
    return(dEAL(y, x, beta, gam_par, lambda, phi_til, phi))
  }
  
  pSurv <- function(y,x, transf_paras_T){
    beta <- transf_paras_T[beta_full_index]
    gam_par <- transf_paras_T[gamma_index]
    lambda <- lambda_inverse_transform(transf_paras_T[lambda_index])
    phi_til = transf_paras_T[phi_til_index(true_lag_degrees)]
    phi = transf_paras_T[phi_index(true_lag_degrees)]
    
    return(pEAL(y, x, beta, gam_par, lambda, phi_til, phi))
  }
  
  qSurv <- function(w,x, transf_paras_T){
    beta <- transf_paras_T[beta_full_index]
    gam_par <- transf_paras_T[gamma_index]
    lambda <- lambda_inverse_transform(transf_paras_T[lambda_index])
    phi_til = transf_paras_T[phi_til_index(true_lag_degrees)]
    phi = transf_paras_T[phi_index(true_lag_degrees)]
    
    return(qEAL(w, x, beta, gam_par, lambda, phi_til, phi))
  }
}

if (true_distr_T == "norm"){
  # transf_paras_T = c(beta_0, beta_T, gam_par)
  
  dSurv <- function(y,x, transf_paras_T){
    beta <- transf_paras_T[beta_full_index]
    z <- y -  x %*% beta
    s <- sigma_fun(x, transf_paras_T[gamma_index])
    
    return(1/s * dnorm(z/s))
  }
  
  pSurv <- function(y,x, transf_paras_T){
    beta <- transf_paras_T[beta_full_index]
    z <- y -  x %*% beta
    s <- sigma_fun(x, transf_paras_T[gamma_index])
    
    return(pnorm(z/s))
  }
  
  qSurv <- function(w, x, transf_paras_T){
    beta <- transf_paras_T[beta_full_index]
    s <- sigma_fun(x, transf_paras_T[gamma_index])
    return(x %*% beta + s * qnorm(w))
  }
}

if (true_distr_T == "exp"){
  # transf_paras_T = c(beta_0, beta_T, gam_par)
  
  dSurv <- function(y,x, transf_paras_T){
    beta <- transf_paras_T[beta_full_index]
    exp_para <- exp(- x %*% beta)
    s <- sigma_fun(x, transf_paras_T[-beta_full_index])
    
    return(1/s*exp(y)*dexp(exp(y)/s, rate = exp_para))
  }
  
  pSurv <- function(y,x, transf_paras_T){
    beta <- transf_paras_T[beta_full_index]
    exp_para <- exp(- x %*% beta)
    s <- sigma_fun(x, transf_paras_T[-beta_full_index])
    
    return(pexp(exp(y)/s, rate = exp_para))
  }
  
  qSurv <- function(w, x, transf_paras_T){
    beta <- transf_paras_T[beta_full_index]
    exp_para <- exp(- x %*% beta)
    s <- sigma_fun(x, transf_paras_T[-beta_full_index])
    
    return(log(s*qexp(w, rate = exp_para)))
  }
}
########################################################################

############ PART 2: END ######################################################





############ PART 3: ACTUAL SIMULATION ########################################

#### Initialisation of storage structures #####################################
all_llh_true_values <- rep(0, length = simulation_size)
all_mll_estimates <- rep(0, length = simulation_size)
all_uncens_obs_numbers <- rep(0, length = simulation_size)
variances_T_on_X <- rep(0, length = simulation_size)
variances_C_on_X <- rep(0, length = simulation_size)
means_T_on_X <- rep(0, length = simulation_size)
means_C_on_X <- rep(0, length = simulation_size)

all_para_estimates <- vector(mode = "list", length = simulation_size)

sel_deg_left <- rep(0, length = simulation_size)
sel_deg_right <- rep(0, length = simulation_size)

sel_qu_estimates_list <- replicate(length(quantile_levels),
                                   matrix(rep(0, X_selection_size*
                                                simulation_size),
                                          ncol = X_selection_size,
                                          byrow = TRUE),
                                   simplify = FALSE)

sel_qu_true_values_matrix <- matrix(rep(0, X_selection_size *
                                          length(quantile_levels)),
                                    ncol = X_selection_size, byrow = TRUE)
###############################################################################



############# Theoretical quantiles for the covariate selection ###############
for (qu_index in seq_along(quantile_levels)){
  qu_level <- quantile_levels[[qu_index]]
  
  true_quantile_fun <- function(x){
    return(qSurv(qu_level, x, true_transf_paras_T))
  }
  
  sel_qu_true_values_matrix[qu_index,] <- as.vector(
    true_quantile_fun(X_selection))
}
###############################################################################


# to store performance time
tic.clearlog()
tic("Total runtime (sec.)")


for (simulation_index in seq_len(simulation_size)){
  #### Non-quantile level dependent part: sampling, determining starting values,
  # optimal degree selection (using AIC) and performing mll optimisation ####
  
  ### Sample generation ###
  ## Copula & covariate (X) sample ##
  set.seed(copula_seeds[simulation_index])
  cop_sample <- rbicop(n = sample_size, family = true_cop_name,
                       parameters = true_theta)
  
  X <- covariate_sampling(size = sample_size,
                          seed = covariate_seeds[simulation_index])
  
  
  ## Extracting marginal samples T|X and C|X, and Y and Delta ##
  T_on_X <- rep(0, sample_size)
  C_on_X <- rep(0, sample_size)
  
  for (j in seq_len(sample_size)){
    T_on_X[j] <- qSurv(cop_sample[j,1], X[j,], true_transf_paras_T)
    C_on_X[j] <- qCens(cop_sample[j,2], X[j,], true_transf_paras_C)
  }
  
  Y <- pmin(T_on_X, C_on_X)
  Delta <- as.numeric(T_on_X <= C_on_X)
  
  # observed survival times
  T1 = T_on_X[Delta==1]
  X1 = X[Delta==1,]
  
  # censored observations
  C0 = C_on_X[Delta==0]
  X0 = X[Delta==0,]
  
  ## visualisation: only for sim. 1, 21, 41, ... to avoid too many plots ##
  if ((simulation_index %% 20) == 1){
    
    for (j in 1:X_dimension){
      png(filename = paste0(folder_path, "/plot_TC_X", toString(j) , "_sim_",
                            toString(simulation_index), ".png"))
      plot(X[,j + 1], T_on_X, main = paste0("T (black) and C (red) vs. X",
                                            toString(j)))
      lines(X[,j + 1], C_on_X, type = "p", col = "red")
      dev.off()
    }
  }
  
  ## True log likelihood ##
  if (true_distr_T == "EAL"){
    if (true_cop_name == "indep"){
      true_llh <- log_lik_fun_indep(true_transf_paras[-1], true_lag_degrees,
                                    true_cop_name, Y, X, Delta)
    } else {
      true_llh <- log_lik_fun(true_transf_paras, true_lag_degrees, true_cop_name,
                              Y, X, Delta)
    }
  } else { # makes no sense to compare llh over different distributions
    true_llh <- 0
  }
  
  
  ### determining optimal Laguerre degrees using AIC ###
  intermed_res <- deg_sel_AIC_grid_only_T(cop_name = test_cop_name,
                                          Y = Y, X = X, Delta = Delta,
                                          T1, X1, C0, X0,
                                          indep_assumption =
                                            indep_assumption,
                                          max_deg = lag_deg_upper)
  
  
  ### Finalising optimisation with optimal degrees ###
  test_lag_degrees <- intermed_res[[1]]
  current_paras <- intermed_res[[2]]
  
  
  ## Temporary external printing (in case of crash) ##
  est_intermed_temp_file <- paste0(folder_path,
                                   "/estimates_intermed_temporary.txt")
  write(paste0("Simulation index: ", simulation_index),
        file = est_intermed_temp_file, append = TRUE)
  write(toString(as.vector(round(current_paras, DigNum))),
        file = est_intermed_temp_file, append = TRUE)
  write("\n", file = est_intermed_temp_file, append = TRUE)
  #################################
  
  ## Determining final starting values (using intermediate results) ##
  final_init_values <- determine_init_final(current_paras, indep_assumption)
  
  ## Maximum likelihood estimation & resulting parameters ##
  mll_res <- perform_mll_optimisation(test_lag_degrees, test_cop_name,
                                      Y, X, Delta,
                                      init_val_list = final_init_values,
                                      opt_algo = "NMCob",
                                      it_num_constr = it_NMCob_constr,
                                      it_num_unconstr = it_NMCob_unconstr,
                                      indep_assumption = indep_assumption)
  #############################################################################
  
  est_mll <-  mll_res[[1]]
  est_transf_para_vec <- mll_res[[2]]
  est_para_vec <- para_inv_transform(est_transf_para_vec,
                                     cop_name = test_cop_name)
  
  
  
  ## Storage ##############################################
  all_uncens_obs_numbers[simulation_index] <- sum(Delta)
  
  variances_T_on_X[simulation_index] <- var(T_on_X)
  variances_C_on_X[simulation_index] <- var(C_on_X)
  means_T_on_X[simulation_index] <- mean(T_on_X)
  means_C_on_X[simulation_index] <- mean(C_on_X)
  
  all_llh_true_values[simulation_index] <- true_llh
  all_mll_estimates[simulation_index] <- est_mll
  
  all_para_estimates[[simulation_index]] <- est_para_vec
  
  sel_deg_left[simulation_index] <- test_lag_degrees[1]
  sel_deg_right[simulation_index] <- test_lag_degrees[2]
  #########################################################
  
  
  ## Temporary external printing (in case of crash) ##
  est_temp_file <- paste0(folder_path, "/estimates_final_temporary.txt")
  write(paste0("Simulation index: ", simulation_index),
        file = est_temp_file, append = TRUE)
  write(toString(as.vector(round(est_para_vec, DigNum))),
        file = est_temp_file, append = TRUE)
  write("\n", file = est_temp_file, append = TRUE)
  #################################
  
  paras_T_indices <- c(beta_full_index, gamma_index, lambda_index,
                       phi_til_index(test_lag_degrees),
                       phi_index(test_lag_degrees)) + ktau_length_test
  # ktau_length = 0 for indep_assumption, 1 if ktau is present while performing
  # mll estimation. Shift used to omit eta (~ ktau) if present.
  
  est_paras_T <- est_para_vec[paras_T_indices]
  
  est_beta_full <- est_paras_T[beta_full_index]
  est_gam_par <- est_paras_T[gamma_index]
  est_lambda <- est_paras_T[lambda_index]
  est_phi_til <- est_paras_T[phi_til_index(test_lag_degrees)]
  est_phi <- est_paras_T[phi_index(test_lag_degrees)]
  
  
  
  #### Quantile level dependent part ####
  for (qu_index in seq_along(quantile_levels)){
    
    qu_level <- quantile_levels[qu_index]
    
    ### Estimated qu_level-th quantile (based on mll) ###
    est_quantile_fun <- function(x){
      return(qEAL(w = qu_level, x = x, beta = est_beta_full,
                  gam_par = est_gam_par, lambda = est_lambda,
                  phi_til = est_phi_til, phi = est_phi))
    }
    
    
    ## Estimated qu_level-th quantiles of the selected covariate values ##
    selected_est_quantiles <- as.vector(est_quantile_fun(X_selection))
    
    
    ## Storage ##############################################
    sel_qu_estimates_list[[qu_index]][simulation_index,] <-
      t(selected_est_quantiles)
    #########################################################
  }
  
  print(paste0("Done loop: simulation_index ", toString(simulation_index)))
  print(Sys.time())
}


# retrieve elapsed time
toc(log = TRUE)
log.lst <- tic.log(format = FALSE)
runtime <- round(as.numeric(unlist(lapply(
  log.lst, function(x) x$toc - x$tic))), DigNum)
############ PART 3: END ######################################################





############ PART 4: PERFORMANCE ASSESMENT & STORAGE ##########################

### for resulting parameter estimates
para_summary_stat <- para_performance_summary(ext_print = TRUE,
                                              ext_boxplots = TRUE)
# includes external printing, if asked for, otherwise put ext_print = FALSE

### for quantiles (for covariate selection) ###
qu_performance_summary <- get_qu_performance()

sel_qu_means <- qu_performance_summary[[1]]
sel_qu_RMSE <- qu_performance_summary[[2]]
sel_qu_var <- qu_performance_summary[[3]]
sel_qu_bias <- qu_performance_summary[[4]]
sel_qu_biasrel <- qu_performance_summary[[5]]

print_qu_performance_summary()

# store settings externally
external_print_fun()

############ PART 4: END ######################################################

