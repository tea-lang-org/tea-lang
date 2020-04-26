import tea

data_path = "./ar_tv_long.csv"

variables = [
    {
        'name': 'ID',
        'data type': 'ratio'
    },
    {
        'name': 'Condition',
        'data type': 'nominal',
        'categories': ['AR', 'TV']
    },
    {
        'name': 'Score',
        'data type': 'ordinal',
        'categories': [1,2,3,4,5]
    }
]

experimental_design = {
    'study type': 'experiment',
    'independent variables': 'Condition',
    'dependent variables': 'Score'
}

assumptions = {
    'Type I (False Positive) Error Rate': 0.01969
}

tea.data(data_path, key='ID')
tea.define_variables(variables)
tea.define_study_design(experimental_design)
tea.assume(assumptions)
results = tea.hypothesize(['Score', 'Condition'], ['Condition:AR > TV'])

'''
Results:
--------------
Test: mannwhitney_u
***Test assumptions:
Exactly one explanatory variable: Condition
Exactly one explained variable: Score
Independent (not paired) observations: Condition
Variable is categorical: Condition
Variable has two categories: Condition
Continuous OR ORDINAL (not nominal) data: Score

***Test results:
name = Mann Whitney U Test
test_statistic = 442.50000
p_value = 0.03938
adjusted_p_value = 0.01969
alpha = 0.01969
dof = 26
Effect size:
A12 = 0.65459
Null hypothesis = There is no difference in medians between Condition = AR and Condition = TV on Score.
Interpretation = t(26) = 442.50000, p = 0.01969. Reject the null hypothesis at alpha = 0.01969. The median of Score for Condition = AR is significantly greater than the median for Condition = TV. The effect size is A12 = 0.65459. The effect size is the magnitude of the difference, which gives a holistic view of the results [1].
[1] Sullivan, G. M., & Feinn, R. (2012). Using effect size—or why the P value is not enough. Journal of graduate medical education, 4(3), 279-282.
'''
