# Least CM Degree

This repository holds code and lists for the paper *The least degree of a CM point on a modular curve* by Pete L. Clark, Tyler Genao, Paul Pollack, and Frederick Saia.

## Sporadic Checks

- 'sporadic_checks_X0_X1.m': Knowing there are finitely many N for which the modular curves X_1(N) and X_0(N) may not have a sporadic CM point, this code is for checking such N further to see if we can guarantee a sporadic point. Specifically, we use the theorem of Faltings-Frey combined with lower bounds on the gonality of these curves and upper bounds on the least degree of a CM point on them. 

- 'sporadic_checks_XMN.m': Knowing there are finitely many pairs (M,N) with M|N for which the modular curve X(M,N) may not have a sporadic CM point, this code is for checking such pairs further to see if we can guarantee a sporadic point. Specifically, we use the theorem of Faltings-Frey combined with a lower bound on the gonality of X(M,N) and an upper bound on the least degree of a CM point on X(M,N). 

- 'further_bads_X0_X1.m': The sequence of N for which techniques from 'sporadic_checks_X0_X1' do not guarantee a sporadic CM point on X_0(N) and X_1(N). 

- 'further_bads_XMN.m': The sequence of pairs (M,N) for which techniques from 'sporadic_checks_XMN' do not guarantee a sporadic CM point on X(M,N). 

## Least Degrees

### X1

- 'least_degreesX1.m': The aim of this code is to compute, for an integer N >= 2, the least degree over Q of a CM point on the modular curve X_1(N) (via methods of Bourdon-Clark '19). These computations are then used to try to guarantee the existence of a sporadic CM point on X_1(N) via Frey-Faltings and lower bounds on the gonality of X_1(N). We also prove there can be no sporadic CM point on X_1(N) for some N using the least degree computation combined with upper bounds on the gonality of X_1(N) from Derickx-van Hoeij '13. 

- 'hyper_bads_X1.m': Sequence of 297 naturals N in 'further_bads_X0_X1.m' such that X_1(N) is guarunteed a sporadic CM point via methods in 'least_degreesX1.m'. This corresponds to the set F_1 in our paper. 

- 'no_sporadic_CM_X1.m': Sequence of the 67 values of N for which we prove X_1(N) has no sporadic CM point. 

- 'dcm_list_X1_1mil.m': List of least CM degree values for X_1(N) for N up to 1,000,000, each including a minimizing order. 

- 'dcm_list_all_min_orders_X1_10k.m': List of least CM degree values for X_1(N) for N up to 10,000, with a list of all the minimizing orders of class number up to 100. 

### X0 

- 'least_degreesX0.m': The aim of this code is to compute, for an integer N >= 2, the least degree over Q of a CM point on the modular curve X_0(N). We directly use computations from 'least_degreesX1.m' to do this. These computations are then used to try to guarantee the existence of a sporadic CM point on X_0(N) via Frey-Faltings and lower bounds on the gonality of X_0(N). We also prove there can be no sporadic CM point on X_0(N) for some N using the least degree computation combined with both upper bounds on the gonality of X_0(N) as well as knowledge of all N with delta(X_0(N)) <=2. 

- 'hyper_bads_X0.m': Sequence of 359 naturals N in 'further_bads_X0_X1.m' such that X_0(N) is guarunteed a sporadic CM point via methods in 'least_degreesX0.m'. This corresponds to the set F_0 in our paper.

- 'no_sporadic_CM_X0.m': Sequence of the 50 values of N for which we prove X_0(N) has no sporadic CM point. 

- 'dcm_list_X0_1mil': List of least CM degree values for X_0(N) for N up to 1,000,000, each including a minimizing order. 

### XMN

- 'least_degreesXMN.m': The aim of this code is to compute, for integers M,N with M|N and N >= 2, the least degree over Q(\zeta_M) of a CM point on the modular curve X(M,N) (via methods of Bourdon-Clark '19). These computations are then used to try to guarantee the existence of a sporadic CM point on X(M,N) via Frey-Faltings and lower bounds on the gonality of X(M,N). We also prove there can be no sporadic CM point on X(M,N) for some M,N using the least degree computation combined with upper bounds on the gonality of X(M,N) derived from on those of X_1(N) Derickx-van Hoeij '13. 

- 'hyper_bads_XMN.m': Sequence of 480 pairs (M,N) in 'further_bads_XMN.m' such that X(M,N) is guarunteed a sporadic CM point via methods in 'least_degreesXMN.m'.

- 'no_sporadic_CM_XMN.m': Sequence of the 89 pairs (M,N) for which we prove X(M,N) has no sporadic CM point. 

- 'dcm_bounds_list_XMN_100': List of upper bounds on least CM degree values for X(M,N) for all M|N for N up to 100, including a list of all orders of class number up to 100 yielding this upper bound. For N<53, these least CM degree values are exact. 

