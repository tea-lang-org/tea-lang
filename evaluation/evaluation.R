# Author: Eunice Jun
# Last updated: March 5, 2019
## Description:
# Evaluation is based on R tutorials found in the book entitled 
# R in Action: Data Analysis and graphics with R by Robert I. Kabacoff (2011).


# Independent T-Test (p. 164-165)
library (MASS)
t.test(Prob ~ So, data=UScrime)
