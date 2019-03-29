# Author: Eunice Jun
# Last updated: March 25, 2019
## Description:
# Evaluation is based on R tutorials found in the book entitled 
# R in Action: Data Analysis and graphics with R by Robert I. Kabacoff (2011).

## Command for taking a dataset (in R's core) and writing out/saving as CSV
# write.csv(file="statex77.csv", state.x77)

library(reshape)
base_path = "/Users/emjun/Git/tea-lang/evaluation/discovering-statistics-using-r/"

####### CORRELATIONS #######
### Pearson Correlation (p. 159-164)
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

### Pearson Correlation (p. 221)
# Field et al. (p. 219 - 221)
# Code from Supplementary Material
# Without p-values
path = paste(base_path, "exam.dat", sep="")
examData<- read.delim(path, header=TRUE)
examData2 <- examData[,c("Exam", "Anxiety", "Revise")]
cor(examData2)
# With p-values 
library(Hmisc)
examMatrix<-as.matrix(examData[, c("Exam", "Anxiety", "Revise")])
Hmisc::rcorr(examMatrix)
Hmisc::rcorr(as.matrix(examData[, c("Exam", "Anxiety", "Revise")]))

cor.test(examData$Anxiety, examData$Exam)
cor.test(examData$Revise, examData$Exam)
cor.test(examData$Anxiety, examData$Revise)

### Spearman Rho Correlation (p. 223 - 225)
# Field et al. 
path = paste(base_path, "liar.dat", sep="")
liarData = read.delim(path,  header = TRUE)
head(liarData)

cor(liarData$Position, liarData$Creativity, method = "spearman")
cor.test(liarData$Position, liarData$Creativity, alternative = "less", method = "spearman")

liarMatrix<-as.matrix(liarData[, c("Position", "Creativity")])
rcorr(liarMatrix)

### Kendall's tau Correlation (p. 225 - 226)
# Field et al. 
cor(liarData$Position, liarData$Creativity, method = "kendall")
cor(liarData$Position, liarData$Creativity, method = "spearman")
cor.test(liarData$Position, liarData$Creativity, alternative = "less", method = "pearson")

### Pointbiseral (p. 229 -233)
# Field et al.
path = paste(base_path,"pbcorr.csv", sep="")
catData = read.csv(path, header = TRUE)
cor.test(catData$time, catData$gender)
cor.test(catData$time, catData$recode)
catFrequencies<-table(catData$gender)
prop.table(catFrequencies)

# polyserial(catData$time, catData$gender)
#####################

####### BIVARIATE COMPARISON OF MEANS #######

### Independent T-Test 
# Kabacoff (p. 164-165)
library (MASS)
t.test(Prob ~ So, data=UScrime, var.equal=TRUE)
# could also be written as 
# t.test(y1, y2) # y1 and y2 dependent variables for the two groups
wilcox.test(Prob ~ So, data=UScrime)

### Paired T-Test 
wide_path = paste(base_path, "spiderWide.dat", sep="")
long_path = paste(base_path, "spiderLong.dat", sep="")
spiderWide = read.delim(wide_path,  header = TRUE)
spiderLong = read.delim(long_path,  header = TRUE)
# stat.desc(spiderWide, basic = FALSE, norm = TRUE)

dep.t.test2<-t.test(Anxiety ~ Group, data = spiderLong, paired = TRUE)
dep.t.test2

### Wilcoxon Signed Rank ###
path = paste(base_path, "Drug.dat", sep="")
drugData = read.delim(path,  header = TRUE)
drugData$BDIchange<-drugData$wedsBDI-drugData$sundayBDI
# by(drugData$BDIchange, drugData$drug, stat.desc, basic = FALSE, norm = TRUE)
alcoholData = drugData[drugData$drug == 'Alcohol',1:3]
ecstasyData = drugData[drugData$drug == 'Ecstasy',1:3]

alcoholData_long <- melt(alcoholData, id=c("drug")) 
ecstasyData_long <- melt(ecstasyData, id=c("drug")) 

alcoholModel<-wilcox.test(alcoholData$wedsBDI, alcoholData$sundayBDI,  paired = TRUE, correct= FALSE)
alcoholModel
ecstasyModel<-wilcox.test(ecstasyData$wedsBDI, ecstasyData$sundayBDI, paired = TRUE, correct= FALSE)
ecstasyModel

rFromWilcox(alcoholModel, 20)
rFromWilcox(ecstasyModel, 20)

long_drugData <- melt(a)

# boxplot<-ggplot(drugData, aes(drug, BDIchange)) + geom_boxplot()
# boxplot

# alcoholData<-subset(drugData, drug == "Alcohol")
# ecstasyData<-subset(drugData, drug == "Ecstasy")

## SKIP: ANALYSIS IN WIDE FORMAT
# Kabacoff (p. 166)
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

######################

####### MULTIVARIATE #######
### One-Way ANOVA (F-test)
## From Kabacoff (p. 225)
## Originally from Westfall, Tombia, Rom, & Hochberg (1999)
library(multcomp)
attach(cholesterol)
table(trt)

aggregate(response, by=list(trt), FUN=mean)
aggregate(response, by=list(trt), FUN=sd) 
fit <- aov(response ~ trt)
summary(fit)

# This does not work: 
kw_fit <- kruskal.test(response ~ trt, data=cholesterol)
summary(kw_fit)

### IV. Kruskall-Wallis (non-parametric alternative to ANVOA)
## From Field et al. Discovering Statistics Using R
soya_file = '/Users/emjun/Git/tea-lang/evaluation/discovering-statistics-using-r/soya.dat'

Sperm<-c(0.35, 0.58, 0.88, 0.92, 1.22, 1.51, 1.52, 1.57, 2.43, 2.79, 3.40, 4.52, 4.72, 6.90, 7.58, 7.78, 9.62, 10.05, 10.32, 21.08, 0.33, 0.36, 0.63, 0.64, 0.77, 1.53, 1.62, 1.71, 1.94, 2.48, 2.71, 4.12, 5.65, 6.76, 7.08, 7.26, 7.92, 8.04, 12.10, 18.47, 0.40, 0.60, 0.96, 1.20, 1.31, 1.35, 1.68, 1.83, 2.10, 2.93, 2.96, 3.00, 3.09, 3.36, 4.34, 5.81, 5.94, 10.16, 10.98, 18.21, 0.31, 0.32, 0.56, 0.57, 0.71, 0.81, 0.87, 1.18, 1.25, 1.33, 1.34, 1.49, 1.50, 2.09, 2.70, 2.75, 2.83, 3.07, 3.28, 4.11)
Soya<-gl(4, 20, labels = c("No Soya", "1 Soya Meal", "4 Soya Meals", "7 Soya Meals"))
soyaData<-data.frame(Sperm, Soya)
cor.test(soyaData$Soya, soyaData$Sperm) # This checks out with Tea's output for spearman


soyaData<-read.delim(soya_file, header = TRUE)
# The below line is from the supplementary materials, but it gives "NA" for all Soya values
# soyaData$Soya<-factor(soyaData$Soya, levels = levels(soyaData$Soya)[c(4, 1, 2, 3)])
soyaData$Soya<- as.factor(soyaData$Soya)

# From supplementary material, but stat.desc is undefined? 
# by(soyaData$Sperm, soyaData$Soya, stat.desc, basic=FALSE)
# by(soyaData$Sperm, soyaData$Soya, stat.desc, desc = FALSE, basic=FALSE, norm=TRUE)
library(car)
leveneTest(soyaData$Sperm, soyaData$Soya)

kruskal.test(Sperm ~ Soya, data = soyaData)
soyaData$Ranks<-rank(soyaData$Sperm)
by(soyaData$Ranks, soyaData$Soya, mean)


### IV. Repeated Measures ANOVA
# From Kabacoff (p. 237)
w1b1 <- subset(CO2, Treatment == 'chilled')
# conc is within subjects
# type is between subjects
fit <- aov(uptake ~ conc*Type + Error(Plant/(conc), w1b1), data=CO2)
summary(fit)

par(las=2)
par(mar=c(10,4,4,2))
with(w1b1, interaction.plot(conc, Type, uptake, 
                            type='b', col=c('red','blue'), pch=c(16, 18),
                            main='Interaction Plot for Plant Type and Concentration'))
boxplot(uptake ~ Type*conc, data = w1b1, col=(c('gold', 'green')), 
        main='Chilled Quebec and Mississippi PLants', 
        ylab='Carbon dioxide uptake rate')

##################

######## PROPROTIONS #######
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




