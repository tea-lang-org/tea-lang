# Author: Eunice Jun
# Last updated: March 5, 2019
## Description:
# Evaluation is based on R tutorials found in the book entitled 
# R in Action: Data Analysis and graphics with R by Robert I. Kabacoff (2011).


# Independent T-Test (p. 164-165)
library (MASS)
t.test(Prob ~ So, data=UScrime)
# could also be written as 
# t.test(y1, y2) # y1 and y2 dependent variables for the two groups
wilcox.test(Prob ~ So, data=UScrime)

# Dependent T-Test (p. 166)
sapply(UScrime[c("U1", "U2")], function(x) (c(mean=mean(x), sd=sd(x))))
# with: Evaluate an R expression in an environment constructed from data, possibly modifying (a copy of) the original data.
# **possibly**, **copy of data**
with(UScrime, t.test(U1, U2, paired=TRUE))
#t.test(U1, U2, data=UScrime, paired=TRUE) # not valid
t.test(UScrime$U1, UScrime$U2, data=UScrime, paired=TRUE) 


# Independent Non-parametric Test: Wilcoxon rank sum test AKA Mann Whitney U test
# Default: two-tailed test
# Can add options: exact, alternative=less, alternative=greater
wilcox.test(Prob ~ So, data=UScrime)
# or wilcox.test(y1, y2) -- see above
with(UScrime, by(Prob, So, median))


# Dependent Non-parametric Test: Wilcoxon signed-rank test (not even called this in book) -- how are you supposed to learn if name not used?
sapply(UScrime[c("U1", "U2")], median)
with(UScrime, wilcox.test(U1, U2, paired=TRUE))
# WARNING - Not even discussed in book! (may be because of when warnings were added to the code base, etc.)
# Warning message:
# In wilcox.test.default(U1, U2, paired = TRUE) :
# cannot compute exact p-value with ties



