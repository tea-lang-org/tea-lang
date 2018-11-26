# Load data
motivation_paper_dataset <- read.csv("~/Git/tea-lang/data/motivation_paper_dataset.csv")
View(motivation_paper_dataset)
# Print out the number of participants who took each of the three studies
as.data.frame(table(motivation_paper_dataset$study_name))


# Naive way
> mean(motivation_paper_dataset$data_bored)
[1] NA # uh what
> typeof(motivation_paper_dataset$data_bored)
[1] "integer" # so why isn't mean working?
> tapply(motivation_paper_dataset$data_bored, motivation_paper_dataset$study_name, mean)
aesthetics analytic_test_2       color-age 
NA              NA              NA  # hmmmm....
> mean(motivation_paper_dataset$data_bored, na.rm=TRUE) # had to remove those NAs
[1] 3.139474 
> mean(motivation_paper_dataset$data_compare, na.rm=TRUE)
[1] 3.318739
> mean(motivation_paper_dataset$data_fun, na.rm=TRUE)
[1] 4.136851
> mean(motivation_paper_dataset$data_science, na.rm=TRUE)
[1] 3.688274
> mean(motivation_paper_dataset$data_selfLearn, na.rm=TRUE)
[1] 4.221666

#Are the mean motivations for each motivation type significantly different from one another?
#Before I can check that, I have to make sure that the variances are equal, right?
> var(motivation_paper_dataset$data_bored, na.rm=TRUE)
[1] 1.923122
> var(motivation_paper_dataset$data_compare, na.rm=TRUE)
[1] 1.862386
> var(motivation_paper_dataset$data_fun, na.rm=TRUE)
[1] 0.969039
> var(motivation_paper_dataset$data_science, na.rm=TRUE)
[1] 1.531751
> var(motivation_paper_dataset$data_selfLearn, na.rm=TRUE)
[1] 1.054588

# Are these variances different from one another?
# Can't use F-test because I have more than 2 groups. 
# Bartlett's...but assumes normality
# Levene's....less sensitive to normality. LET'S USE THIS ONE
# Fligner-Killeen....non-parametric test....but also, I have never heard of this test before.

# Oh no. My data is not in the right format. So I have to create subsets of my data to test for variance?!
# ***I FEEL LIKE I SHOULDNT HAVE TO DO THIS! ****
> motivations_only <- motivation_paper_dataset[c(8:12)]
# Above: I have to know the order/number of the columns. 
#This seems hard/annoying if I change my CSV or use a new dataset. Have to manually change each time
> View(motivations_only) #then look at
motivations_only$combined = motivations_only$data_bored
> motivations_only$motivation_type = 'bored' # This was a bad idea. Now all cells are labeled "bored" 
> rbind(motivations_only$combined, motivations_only$data_compare)
# Take 2
# Cancel out/remove bad decisions to start over
> motivations_only$combined <- NULL
> motivations_only$motivation_type <- NULL
> nrow(motivations_only$data_bored)
NULL
> dim(motivations_only)
[1] 7870    5
# Give up on this thread for now. I think I got the insight:
# Even if data is clean, R requires subprocesses/subsets to find characteristics
# about the data along the way of doing a larger, more important analysis.



# Let's be "smarter" about this...
> install.packages("plyr")
> library(plyr)
# remove all participants who do not have values for the motivation types
# can specify when to include, etc. 
clean_dataset <- motivation_paper_dataset[complete.cases(motivation_paper_dataset[,8:12]), ]
> which (colnames(clean_dataset) == 'age')
[1] 47
> clean_dataset <- motivation_paper_dataset[complete.cases(motivation_paper_dataset[,8:12, 47]), ]
# Produce participant demographic info (Table 1)
# Age
> mean(motivation_paper_dataset$age[motivation_paper_dataset$study_name == 'aesthetics'], na.rm=TRUE)
[1] 24.96774
> mean(motivation_paper_dataset$age[motivation_paper_dataset$study_name == 'analytic_test_2'], na.rm=TRUE)
[1] 27.0612
> mean(motivation_paper_dataset$age[motivation_paper_dataset$study_name == 'color-age'], na.rm=TRUE)
[1] 19.78892
# Gender
> mean(motivation_paper_dataset$gender[motivation_paper_dataset$study_name == 'aesthetics'], na.rm=TRUE)
[1] 0.5774194
> mean(motivation_paper_dataset$gender[motivation_paper_dataset$study_name == 'analytic_test_2'], na.rm=TRUE)
[1] 0.5892744
> mean(motivation_paper_dataset$gender[motivation_paper_dataset$study_name == 'color-age'], na.rm=TRUE)
[1] 0.5436893

# RQ 1
cor(clean_dataset[c(8:12, 47)]) 

# RQ 2
> glm(study_name ~ data_bored + data_compare + data_fun + data_science + data_selfLearn, data=clean_dataset)
Error in glm.fit(x = c(1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,  : 
                         NA/NaN/Inf in 'y'
                       In addition: Warning messages:
                         1: In Ops.factor(y, mu) : ‘-’ not meaningful for factors
                       2: In Ops.factor(eta, offset) : ‘-’ not meaningful for factors
                       3: In Ops.factor(y, mu) : ‘-’ not meaningful for factors

> summary(glm(aesthetics ~ data_bored + data_compare + data_fun + data_science + data_selfLearn, data=clean_dataset))
                       
                       Call:
                         glm(formula = aesthetics ~ data_bored + data_compare + data_fun + 
                               data_science + data_selfLearn, data = clean_dataset)
                       
                       Deviance Residuals: 
                         Min       1Q   Median       3Q      Max  
                       -0.2971  -0.1630  -0.1434  -0.1125   0.9494  
                       
                       Coefficients:
                         Estimate Std. Error t value Pr(>|t|)    
                       (Intercept)     0.229098   0.024202   9.466  < 2e-16 ***
                         data_bored     -0.001098   0.003185  -0.345  0.73041    
                       data_compare    0.010634   0.003336   3.188  0.00144 ** 
                         data_fun       -0.013729   0.004657  -2.948  0.00321 ** 
                         data_science    0.015013   0.003679   4.081 4.53e-05 ***
                         data_selfLearn -0.026011   0.004618  -5.633 1.84e-08 ***
                         ---
                         Signif. codes:  0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1
                       
                       (Dispersion parameter for gaussian family taken to be 0.1264846)
                       
                       Null deviance: 917.28  on 7198  degrees of freedom
                       Residual deviance: 909.80  on 7193  degrees of freedom
                       AIC: 5553
                       
                       Number of Fisher Scoring iterations: 2

> summary(glm(thinking ~ data_bored + data_compare + data_fun + data_science + data_selfLearn, data=clean_dataset))
                       
                       Call:
                         glm(formula = thinking ~ data_bored + data_compare + data_fun + 
                               data_science + data_selfLearn, data = clean_dataset)
                       
                       Deviance Residuals: 
                         Min       1Q   Median       3Q      Max  
                       -0.6789  -0.4629  -0.2662   0.5012   0.9403  
                       
                       Coefficients:
                         Estimate Std. Error t value Pr(>|t|)    
                       (Intercept)     0.105303   0.032995   3.191  0.00142 ** 
                         data_bored      0.006494   0.004343   1.495  0.13484    
                       data_compare    0.009139   0.004548   2.010  0.04452 *  
                         data_fun       -0.026557   0.006349  -4.183 2.91e-05 ***
                         data_science   -0.016382   0.005015  -3.267  0.00109 ** 
                         data_selfLearn  0.107679   0.006295  17.105  < 2e-16 ***
                         ---
                         Signif. codes:  0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1
                       
                       (Dispersion parameter for gaussian family taken to be 0.2350913)
                       
                       Null deviance: 1772.7  on 7198  degrees of freedom
                       Residual deviance: 1691.0  on 7193  degrees of freedom
                       AIC: 10015
                       
                       Number of Fisher Scoring iterations: 2

> summary(glm(colorage ~ data_bored + data_compare + data_fun + data_science + data_selfLearn, data=clean_dataset))
                       
                       Call:
                         glm(formula = colorage ~ data_bored + data_compare + data_fun + 
                               data_science + data_selfLearn, data = clean_dataset)
                       
                       Deviance Residuals: 
                         Min       1Q   Median       3Q      Max  
                       -0.7670  -0.4017  -0.3300   0.5624   0.8269  
                       
                       Coefficients:
                         Estimate Std. Error t value Pr(>|t|)    
                       (Intercept)     0.665599   0.032914  20.222  < 2e-16 ***
                         data_bored     -0.005397   0.004332  -1.246    0.213    
                       data_compare   -0.019772   0.004536  -4.359 1.33e-05 ***
                         data_fun        0.040285   0.006333   6.361 2.12e-10 ***
                         data_science    0.001370   0.005003   0.274    0.784    
                       data_selfLearn -0.081668   0.006280 -13.005  < 2e-16 ***
                         ---
                         Signif. codes:  0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1
                       
                       (Dispersion parameter for gaussian family taken to be 0.2339373)
                       
                       Null deviance: 1743.3  on 7198  degrees of freedom
                       Residual deviance: 1682.7  on 7193  degrees of freedom
                       AIC: 9979.9
                       
                       Number of Fisher Scoring iterations: 2

# RQ 3
> as.data.frame(table(clean_dataset$satisficing))
Var1 Freq
1             5103
2     engaged  168
3 not engaged 1928

imc <- clean_dataset[complete.cases(clean_dataset[,40]),] # nope not this
> imc <- clean_dataset[clean_dataset$satisficing != "",]
# easier to do direct arithmetic than use a function
> 168/1928
[1] 0.08713693
> imc$satisificing_num <- ifelse(imc$satisficing == "engaged", 1, 0)
# OH NO. I misspelled "satisficing"
> summary(glm(satisificing_num ~ data_bored + data_compare + data_fun + data_science + data_selfLearn + study_name, data = imc))

Call:
  glm(formula = satisificing_num ~ data_bored + data_compare + 
        data_fun + data_science + data_selfLearn + study_name, data = imc)

Deviance Residuals: 
  Min        1Q    Median        3Q       Max  
-0.20773  -0.10773  -0.06936  -0.03673   1.00383  

Coefficients:
  Estimate Std. Error t value Pr(>|t|)    
(Intercept)                0.156447   0.032358   4.835 1.43e-06 ***
  data_bored                -0.028099   0.004396  -6.392 2.01e-10 ***
  data_compare               0.004207   0.004692   0.897  0.37001    
data_fun                   0.007483   0.006077   1.231  0.21829    
data_science               0.009984   0.005060   1.973  0.04860 *  
  data_selfLearn            -0.008182   0.006172  -1.326  0.18508    
study_nameanalytic_test_2 -0.038893   0.017003  -2.287  0.02227 *  
  study_namecolor-age       -0.043260   0.016718  -2.588  0.00973 ** 
  ---
  Signif. codes:  0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1

(Dispersion parameter for gaussian family taken to be 0.07198141)

Null deviance: 154.53  on 2095  degrees of freedom
Residual deviance: 150.30  on 2088  degrees of freedom
AIC: 442.87

Number of Fisher Scoring iterations: 2


> summary(glm(satisificing_num ~ data_bored + data_compare + data_fun + data_science + data_selfLearn + study_name + age + gender, data = imc))

Call:
  glm(formula = satisificing_num ~ data_bored + data_compare + 
        data_fun + data_science + data_selfLearn + study_name + age + 
        gender, data = imc)

Deviance Residuals: 
  Min        1Q    Median        3Q       Max  
-0.31051  -0.11769  -0.07520  -0.03025   1.01506  

Coefficients:
  Estimate Std. Error t value Pr(>|t|)    
(Intercept)                0.1134408  0.0416573   2.723 0.006533 ** 
  data_bored                -0.0287716  0.0053261  -5.402 7.55e-08 ***
  data_compare               0.0033889  0.0056426   0.601 0.548197    
data_fun                   0.0061756  0.0073431   0.841 0.400464    
data_science               0.0097885  0.0061898   1.581 0.113978    
data_selfLearn            -0.0096742  0.0077141  -1.254 0.209986    
study_nameanalytic_test_2 -0.0482432  0.0182900  -2.638 0.008426 ** 
  study_namecolor-age       -0.0168151  0.0195490  -0.860 0.389831    
age                        0.0019122  0.0005773   3.312 0.000945 ***
  gender                     0.0305415  0.0129211   2.364 0.018209 *  
  ---
  Signif. codes:  0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1

(Dispersion parameter for gaussian family taken to be 0.07810694)

Null deviance: 134.83  on 1662  degrees of freedom
Residual deviance: 129.11  on 1653  degrees of freedom
(433 observations deleted due to missingness)
AIC: 491.25

Number of Fisher Scoring iterations: 2

# HOW IS THE DUMMY GROUP CHOSEN??

# To do odds ratios, the data needs to be in a different format -- OMG! yet another subset/re-representation of data. 
# More opportunities for bugs....

#RQ 4
> summary(glm(isStdImi0 ~ data_bored + data_compare + data_fun + data_science + data_selfLearn + study_name, data = imc))

Call:
  glm(formula = isStdImi0 ~ data_bored + data_compare + data_fun + 
        data_science + data_selfLearn + study_name, data = imc)

Deviance Residuals: 
  Min        1Q    Median        3Q       Max  
-0.28315  -0.12651  -0.09316  -0.05586   1.02058  

Coefficients:
  Estimate Std. Error t value Pr(>|t|)    
(Intercept)                0.275683   0.044016   6.263 4.83e-10 ***
  data_bored                 0.010510   0.005678   1.851 0.064357 .  
data_compare               0.019522   0.006124   3.188 0.001462 ** 
  data_fun                  -0.021069   0.008036  -2.622 0.008832 ** 
  data_science              -0.012218   0.006792  -1.799 0.072243 .  
data_selfLearn            -0.028227   0.008469  -3.333 0.000879 ***
  study_nameanalytic_test_2 -0.025119   0.021505  -1.168 0.242963    
study_namecolor-age       -0.018724   0.022033  -0.850 0.395558    
---
  Signif. codes:  0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1

(Dispersion parameter for gaussian family taken to be 0.09132733)

Null deviance: 150.49  on 1611  degrees of freedom
Residual deviance: 146.49  on 1604  degrees of freedom
(484 observations deleted due to missingness)
AIC: 726.63

Number of Fisher Scoring iterations: 2


> summary(glm(isStdImi0 ~ data_bored + data_compare + data_fun + data_science + data_selfLearn + study_name + age + gender, data = imc))

Call:
  glm(formula = isStdImi0 ~ data_bored + data_compare + data_fun + 
        data_science + data_selfLearn + study_name + age + gender, 
      data = imc)

Deviance Residuals: 
  Min        1Q    Median        3Q       Max  
-0.29089  -0.12604  -0.08990  -0.05352   1.02833  

Coefficients:
  Estimate Std. Error t value Pr(>|t|)    
(Intercept)                0.2787068  0.0481953   5.783  8.9e-09 ***
  data_bored                 0.0124585  0.0059891   2.080  0.03767 *  
  data_compare               0.0180169  0.0063178   2.852  0.00441 ** 
  data_fun                  -0.0216891  0.0082233  -2.638  0.00844 ** 
  data_science              -0.0150385  0.0069732  -2.157  0.03119 *  
  data_selfLearn            -0.0290758  0.0086808  -3.349  0.00083 ***
  study_nameanalytic_test_2 -0.0263925  0.0214767  -1.229  0.21930    
study_namecolor-age       -0.0182617  0.0228478  -0.799  0.42425    
age                        0.0002955  0.0006375   0.464  0.64305    
gender                     0.0097681  0.0145839   0.670  0.50310    
---
  Signif. codes:  0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1

(Dispersion parameter for gaussian family taken to be 0.09043948)

Null deviance: 141.69  on 1530  degrees of freedom
Residual deviance: 137.56  on 1521  degrees of freedom
(565 observations deleted due to missingness)
AIC: 677.65

Number of Fisher Scoring iterations: 2

                       
# RQ 5
                       > summary(glm(finished_study ~ data_bored + data_compare + data_fun + data_science + data_selfLearn + study_name, data=clean_dataset))
                       
                       Call:
                         glm(formula = finished_study ~ data_bored + data_compare + data_fun + 
                               data_science + data_selfLearn + study_name, data = clean_dataset)
                       
                       Deviance Residuals: 
                         Min        1Q    Median        3Q       Max  
                       -0.99067   0.04438   0.11696   0.22329   0.49501  
                       
                       Coefficients:
                         Estimate Std. Error t value Pr(>|t|)    
                       (Intercept)                0.478948   0.027081  17.686  < 2e-16 ***
                         data_bored                -0.010074   0.003320  -3.034  0.00242 ** 
                         data_compare               0.002396   0.003481   0.688  0.49132    
                       data_fun                   0.012531   0.004866   2.575  0.01005 *  
                         data_science               0.021433   0.003839   5.583 2.45e-08 ***
                         data_selfLearn             0.019910   0.004909   4.056 5.05e-05 ***
                         study_nameanalytic_test_2  0.240446   0.013194  18.224  < 2e-16 ***
                         study_namecolor-age        0.107665   0.013226   8.140 4.61e-16 ***
                         ---
                         Signif. codes:  0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1
                       
                       (Dispersion parameter for gaussian family taken to be 0.1373583)
                       
                       Null deviance: 1064.61  on 7198  degrees of freedom
                       Residual deviance:  987.74  on 7191  degrees of freedom
                       AIC: 6148.7
                       
                       Number of Fisher Scoring iterations: 2

> summary(glm(finished_study ~ data_bored + data_compare + data_fun + data_science + data_selfLearn + study_name + age + gender, data=clean_dataset))
                       
                       Call:
                         glm(formula = finished_study ~ data_bored + data_compare + data_fun + 
                               data_science + data_selfLearn + study_name + age + gender, 
                             data = clean_dataset)
                       
                       Deviance Residuals: 
                         Min        1Q    Median        3Q       Max  
                       -1.01202  -0.00135   0.00464   0.01235   0.22371  
                       
                       Coefficients:
                         Estimate Std. Error t value Pr(>|t|)    
                       (Intercept)                0.7791801  0.0150445  51.792   <2e-16 ***
                         data_bored                -0.0010851  0.0017198  -0.631   0.5281    
                       data_compare               0.0009442  0.0017778   0.531   0.5954    
                       data_fun                   0.0018247  0.0025109   0.727   0.4674    
                       data_science               0.0041963  0.0019726   2.127   0.0334 *  
                         data_selfLearn             0.0001465  0.0025949   0.056   0.9550    
                       study_nameanalytic_test_2  0.1883771  0.0064528  29.193   <2e-16 ***
                         study_namecolor-age        0.1958390  0.0068101  28.757   <2e-16 ***
                         age                        0.0001665  0.0001618   1.029   0.3037    
                       gender                    -0.0039564  0.0041530  -0.953   0.3408    
                       ---
                         Signif. codes:  0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1
                       
                       (Dispersion parameter for gaussian family taken to be 0.02775411)
                       
                       Null deviance: 187.46  on 5752  degrees of freedom
                       Residual deviance: 159.39  on 5743  degrees of freedom
                       (1446 observations deleted due to missingness)
                       AIC: -4282.6
                       
                       Number of Fisher Scoring iterations: 2
                       
# RQ 6

# Examine the variable/column before analyzing
as.data.frame(table(clean_dataset$average_ABS_rating_diff))
# Aesthetics/Visual Preferences study
> summary(glm(average_ABS_rating_diff ~ data_bored + data_compare + data_fun + data_science + data_selfLearn, data=clean_dataset))

Call:
  glm(formula = average_ABS_rating_diff ~ data_bored + data_compare + 
        data_fun + data_science + data_selfLearn, data = clean_dataset)

Deviance Residuals: 
  Min      1Q  Median      3Q     Max  
-486.3  -345.4  -307.3   632.4   759.5  

Coefficients:
  Estimate Std. Error t value Pr(>|t|)    
(Intercept)     374.823     72.893   5.142 3.23e-07 ***
  data_bored       16.985     11.053   1.537    0.125    
data_compare    -10.679     11.820  -0.903    0.367    
data_fun         13.207     15.617   0.846    0.398    
data_science    -21.706     13.270  -1.636    0.102    
data_selfLearn   -6.009     15.408  -0.390    0.697    
---
  Signif. codes:  0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1

(Dispersion parameter for gaussian family taken to be 222531.7)

Null deviance: 240633372  on 1078  degrees of freedom
Residual deviance: 238776493  on 1073  degrees of freedom
(6120 observations deleted due to missingness)
AIC: 16356

Number of Fisher Scoring iterations: 2


#Thinking Style study
> summary(glm(overall_score ~ data_bored + data_compare + data_fun + data_science + data_selfLearn, data=clean_dataset))

Call:
  glm(formula = overall_score ~ data_bored + data_compare + data_fun + 
        data_science + data_selfLearn, data = clean_dataset)

Deviance Residuals: 
  Min       1Q   Median       3Q      Max  
-182.57   -95.77   -80.95   -66.16   943.56  

Coefficients:
  Estimate Std. Error t value Pr(>|t|)    
(Intercept)     184.539     33.439   5.519 3.69e-08 ***
  data_bored        4.085      3.850   1.061  0.28872    
data_compare      2.799      3.969   0.705  0.48073    
data_fun        -17.137      5.793  -2.958  0.00312 ** 
  data_science      1.604      4.383   0.366  0.71442    
data_selfLearn  -11.664      6.599  -1.768  0.07721 .  
---
  Signif. codes:  0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1

(Dispersion parameter for gaussian family taken to be 77998.78)

Null deviance: 247135371  on 3157  degrees of freedom
Residual deviance: 245852146  on 3152  degrees of freedom
(4041 observations deleted due to missingness)
AIC: 44543

Number of Fisher Scoring iterations: 2

# Color Perception study
> summary(glm(num_correctAns ~ data_bored + data_compare + data_fun + data_science + data_selfLearn, data=clean_dataset))

Call:
  glm(formula = num_correctAns ~ data_bored + data_compare + data_fun + 
        data_science + data_selfLearn, data = clean_dataset)

Deviance Residuals: 
  Min      1Q  Median      3Q     Max  
-4464   -2451   -1892   -1292    8667  

Coefficients:
  Estimate Std. Error t value Pr(>|t|)    
(Intercept)    4883.295    423.103  11.542  < 2e-16 ***
  data_bored       69.458     56.618   1.227  0.22000    
data_compare     -9.612     59.779  -0.161  0.87226    
data_fun       -132.498     82.231  -1.611  0.10722    
data_science   -372.594     65.671  -5.674 1.53e-08 ***
  data_selfLearn -209.527     77.392  -2.707  0.00682 ** 
  ---
  Signif. codes:  0 ‘***’ 0.001 ‘**’ 0.01 ‘*’ 0.05 ‘.’ 0.1 ‘ ’ 1

(Dispersion parameter for gaussian family taken to be 17027818)

Null deviance: 5.1739e+10  on 2961  degrees of freedom
Residual deviance: 5.0334e+10  on 2956  degrees of freedom
(4237 observations deleted due to missingness)
AIC: 57732

Number of Fisher Scoring iterations: 2


                       
# TRYING TO CLEAN DATA IN R WHILE DOING ANALYSIS INTRODUCES A WHOLE NEW BAG OF PROBLEMS
is.na(motivation_paper_dataset$data_bored) # gives me a list of TRUE/FALSE for every row
# how do I find the rows that have NA?


##MAIN OBSERVATIONS
- need to manipulate data into subsets
- different tests use different formats of data, so end up having to represent same data in multiple ways, 
say when doing model vs. checking preconditions (mean, variance, etc) 
--> These problems must be exacerbated by categorical data and less so numeric continous data



