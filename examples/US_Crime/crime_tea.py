import tea

tea.data("./UScrime.csv")

variables = [
    {
        'name': 'So',
        'data type': 'nominal',
        'categories': ['0', '1']
    },
    {
        'name': 'Prob',
        'data type': 'ratio',
        'range': [0,1]     # optional
    },
    {
        'name': 'Ineq',
        'data type': 'ratio'
    }
]

study_design = {
    'study type': 'observational study',
    'contributor variables': ['So', 'Prob'],
    'outcome variables': ['Prob', 'Ineq']
}

assumptions = {
    # 'equal variance': [['So', 'Ineq']],
    # 'groups normally distributed': [['So', 'Prob']],
    'Type I (False Positive) Error Rate': 0.05
}

tea.define_variables(variables)
tea.define_study_design(study_design)
tea.assume(assumptions)
# tea.hypothesize(['So', 'Ineq'], ['So:1 > 0'])
# tea.hypothesize(['So', 'Prob'], ['So:1 > 0'])
tea.hypothesize(['Ineq', 'Prob'], ['Ineq ~ -Prob'])

'''
Results:
--------------
Test: kendalltau_corr
***Test assumptions:
Exactly two variables involved in analysis: Prob, Ineq
Continuous OR ORDINAL (not nominal) data: Prob
Continuous OR ORDINAL (not nominal) data: Ineq

***Test results:
name = Kendall's Tau Correlation
test_statistic = 0.39611
p_value = 0.00009
adjusted_p_value = 0.00009
alpha = 0.05
Null hypothesis = There is no relationship between Ineq and Prob.
Interpretation = Reject the null hypothesis at alpha = 0.05. There is a relationship between Ineq and Prob.

Test: spearman_corr
***Test assumptions:
Exactly two variables involved in analysis: Prob, Ineq
Continuous OR ORDINAL (not nominal) data: Prob
Continuous OR ORDINAL (not nominal) data: Ineq

***Test results:
name = Spearman's R Correlation
test_statistic = 0.55087
p_value = 0.00006
adjusted_p_value = 0.00006
alpha = 0.05
Null hypothesis = There is no monotonic relationship between Ineq and Prob.
Interpretation = Reject the null hypothesis at alpha = 0.05. There is a relationship between Ineq and Prob.
'''
