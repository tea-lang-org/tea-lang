import tea
import pandas as pd

d = {'drug': pd.Series(["Ecstasy", "Ecstasy", "Ecstasy", "Alcohol", "Alcohol", "Alcohol"],
                       index=['0', '1', '2', '3', '4', '5']),
     'sundayBDI': pd.Series([15, 35, 16, 16, 15, 20], index=['0', '1', '2', '3', '4', '5']),
     'wedsBDI': pd.Series([28, 35, 35, 5, 6, 30], index=['0', '1', '2', '3', '4', '5']),
     'BDIchange': pd.Series([13, 0, 19, -11, -9, 10], index=['0', '1', '2', '3', '4', '5'])}

df = pd.DataFrame(d)

variables = [
    {
        'name': 'drug',
        'data type': 'nominal',
        'categories': ['Ecstasy', 'Alcohol']
    },
    {
        'name': 'sundayBDI',
        'data type': 'ratio'
    },
    {
        'name': 'wedsBDI',
        'data type': 'ratio'
    },
    {
        'name': 'BDIchange',
        'data type': 'ratio'
    }
]

study_design = {
    'study type': 'observational study',
    'contributor variables': ['drug', 'sundayBDI'],
    'outcome variables': 'BDIchange'
}

assumptions = {
    'Type I (False Positive) Error Rate': 0.01
}

tea.data(df)
tea.define_variables(variables)
tea.define_study_design(study_design)
tea.assume(assumptions)
# tea.hypothesize(['drug', 'BDIchange'], ['drug:Ecstasy > Alcohol'])
tea.hypothesize(['sundayBDI', 'BDIchange'], ['sundayBDI ~ BDIchange'])

'''
Results:
--------------
Test: kendalltau_corr
***Test assumptions:
Exactly two variables involved in analysis: sundayBDI, BDIchange
Continuous OR ORDINAL (not nominal) data: sundayBDI
Continuous OR ORDINAL (not nominal) data: BDIchange

***Test results:
name = Kendall's Tau Correlation
test_statistic = -0.07161
p_value = 0.84549
adjusted_p_value = 0.84549
alpha = 0.01
Null hypothesis = There is no relationship between sundayBDI and BDIchange.
Interpretation = Fail to reject the null hypothesis at alpha = 0.01. There is no relationship between sundayBDI and BDIchange.

Test: spearman_corr
***Test assumptions:
Exactly two variables involved in analysis: sundayBDI, BDIchange
Continuous OR ORDINAL (not nominal) data: sundayBDI
Continuous OR ORDINAL (not nominal) data: BDIchange

***Test results:
name = Spearman's R Correlation
test_statistic = -0.02942
p_value = 0.95588
adjusted_p_value = 0.95588
alpha = 0.01
Null hypothesis = There is no monotonic relationship between sundayBDI and BDIchange.
Interpretation = Fail to reject the null hypothesis at alpha = 0.01. There is no monotonic relationship between sundayBDI and BDIchange.
'''
