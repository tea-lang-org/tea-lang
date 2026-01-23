import tea

''' 
Want to see if Wrestling is correlated with greater athlete Weight
than Swimming, and if Female athletes have a lower Weight than 
Male athletes.
'''

data_path = "./athlete_events_cleaned_weight.csv"

variables = [
    {
        'name': 'ID',
        'data type': 'ratio'
    },
    {
        'name': 'Sport',
        'data type': 'nominal',
        'categories': ['Swimming', 'Wrestling']
    },
    {
        'name': 'Sex',
        'data type': 'nominal',
        'categories': ['M', 'F']
    },
    {
        'name': 'Weight',
        'data type': 'ratio'
        # 'data type' : 'ordinal',
        # 'categories' : [22,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106]
    }
]

study_design = {
    'study type': 'observational study',
    'contributor variables': ['Sport', 'Sex'],
    'outcome variables': 'Weight',
}

assumptions = {
    'groups normally distributed': [['Sport', 'Weight']],
    'Type I (False Positive) Error Rate': 0.05,
}

tea.data(data_path, key='ID')
tea.define_variables(variables)
tea.define_study_design(study_design)
tea.assume(assumptions)
tea.hypothesize(['Sport', 'Weight'], ['Sport:Wrestling > Swimming'])
tea.hypothesize(['Sex', 'Weight'], ['Sex:F < M'])

'''
Results:
--------------
Test: mannwhitney_u
***Test assumptions:
Exactly one explanatory variable: Sport
Exactly one explained variable: Weight
Independent (not paired) observations: Sport
Variable is categorical: Sport
Variable has two categories: Sport
Continuous OR ORDINAL (not nominal) data: Weight

***Test results:
name = Mann Whitney U Test
test_statistic = 53656766.50000
p_value = 0.00000
adjusted_p_value = 0.00000
alpha = 0.05
Effect size:
A12 = 0.53830
Null hypothesis = There is no difference in medians between Sport = Swimming and Sport = Wrestling on Weight.
Interpretation = t(24095) = 53656766.50000, p = 0.00000. Reject the null hypothesis at alpha = 0.05. The median of Weight for Sport = Wrestling is significantly greater than the median for Sport = Swimming. The effect size is A12 = 0.53830. The effect size is the magnitude of the difference, which gives a holistic view of the results [1].
[1] Sullivan, G. M., & Feinn, R. (2012). Using effect size—or why the P value is not enough. Journal of graduate medical education, 4(3), 279-282.

Test: kruskall_wallis
***Test assumptions:
Independent (not paired) observations: Sport
Exactly one explanatory variable: Sport
Exactly one explained variable: Weight
Continuous (not categorical) data: Weight
Variable is categorical: Sport
Variable has two or more categories: Sport

***Test results:
name = Kruskall Wallis
test_statistic = 72.86194
p_value = 0.00000
adjusted_p_value = 0.00000
alpha = 0.05
dof = 1
Null hypothesis = There is no difference in medians between Sport = Swimming, Wrestling on Weight.
Interpretation = t(1) = 72.86194, p = 0.00000. Reject the null hypothesis at alpha = 0.05. There is a difference in medians of Weight for at least one of Sport = Swimming, Wrestling.


Results:
--------------
Test: mannwhitney_u
***Test assumptions:
Exactly one explanatory variable: Sex
Exactly one explained variable: Weight
Independent (not paired) observations: Sex
Variable is categorical: Sex
Variable has two categories: Sex
Continuous OR ORDINAL (not nominal) data: Weight

***Test results:
name = Mann Whitney U Test
test_statistic = 1457738010.00000
p_value = 0.00000
adjusted_p_value = 0.00000
alpha = 0.05
Effect size:
A12 = 0.15910
Null hypothesis = There is no difference in medians between Sex = M and Sex = F on Weight.
Interpretation = t(206221) = 1457738010.00000, p = 0.00000. Reject the null hypothesis at alpha = 0.05. The median of Weight for Sex = F is significantly less than the median for Sex = M. The effect size is A12 = 0.15910. The effect size is the magnitude of the difference, which gives a holistic view of the results [1].
[1] Sullivan, G. M., & Feinn, R. (2012). Using effect size—or why the P value is not enough. Journal of graduate medical education, 4(3), 279-282.

Test: kruskall_wallis
***Test assumptions:
Independent (not paired) observations: Sex
Exactly one explanatory variable: Sex
Exactly one explained variable: Weight
Continuous (not categorical) data: Weight
Variable is categorical: Sex
Variable has two or more categories: Sex

***Test results:
name = Kruskall Wallis
test_statistic = 61996.35428
p_value = 0.00000
adjusted_p_value = 0.00000
alpha = 0.05
dof = 1
Null hypothesis = There is no difference in medians between Sex = M, F on Weight.
Interpretation = t(1) = 61996.35428, p = 0.00000. Reject the null hypothesis at alpha = 0.05. There is a difference in medians of Weight for at least one of Sex = M, F.
'''