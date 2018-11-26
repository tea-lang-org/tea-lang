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



# TRYING TO CLEAN DATA IN R WHILE DOING ANALYSIS INTRODUCES A WHOLE NEW BAG OF PROBLEMS
is.na(motivation_paper_dataset$data_bored) # gives me a list of TRUE/FALSE for every row
# how do I find the rows that have NA?


