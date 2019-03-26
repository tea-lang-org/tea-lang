# Author: Eunice Jun
# Last updated: March 25, 2019
## Description:
# Evaluation is based on R tutorials found in the book entitled 
# R in Action: Data Analysis and graphics with R by Robert I. Kabacoff (2011).

## Command for taking a dataset (in R's core) and writing out/saving as CSV
# write.csv(file="statex77.csv", state.x77)


### I. Correlation (p. 159-164)
# Using state.x77 dataset from base R package
states <- state.x77[,1:6] # Remove Frost and Area columns from original state.x77 dataset
x <- states[,c("Population", "Income", "Illiteracy", "HS Grad")]
y <- states[,c("Life Exp", "Murder")]
cor(x, y)
# "This code tests the null hypothesis that the Pearson correlation between life expectancy 
# and merder rate is 0. Assuming that the population correlation is 0, you'd expect 
# to see a sample correlation as larage as 0.703 less than 1 time out of 10 million 
# (that is, p = 1.258e-08). 
# In base R package, can only test correlation between two variables at a time. 
cor.test(states[,3], states[,5])

### II. Contingency Tables (for comparing categorical data)
## From Field et al. Discovering Statistics Using R
library(gmodels)
catData <- read.delim("/Users/emjun/Git/tea-lang/evaluation/discovering-statistics-using-r/cats.dat", header=TRUE)
food <- c(10, 28)
affection <- c(114, 48)
catsTable <- cbind(food, affection) 
CrossTable(catsData$Training, catsData$Dance, fisher = TRUE, chisq = TRUE, expected = TRUE, sresid = TRUE, format = "SPSS")
# Equivalent to the above
#CrossTable(catsTable, fisher = TRUE, chisq = TRUE, expected = TRUE, sresid = TRUE, format = "SPSS")
#CrossTable(catsData$Training, catsData$Dance, fisher = TRUE, chisq = TRUE, expected = TRUE, prop.c = FALSE, prop.t = FALSE, prop.chisq = FALSE,  sresid = TRUE, format = "SPSS")




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



