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
    'outcome variables': ['BDIchange', 'wedsBDI']
}

assumptions = {
    'Type I (False Positive) Error Rate': 0.01
}

tea.data(df)
tea.define_variables(variables)
tea.define_study_design(study_design)
tea.assume(assumptions)
tea.hypothesize(['drug', 'wedsBDI'], ['drug:Ecstasy > Alcohol'])
# tea.hypothesize(['sundayBDI', 'BDIchange'], ['sundayBDI ~ BDIchange'])

'''
Results:
--------------
Test: pointbiserial_corr_a
***Test assumptions:
Exactly two variables involved in analysis: drug, wedsBDI
Continuous (not categorical) data: wedsBDI
Normal distribution: wedsBDI: NormalTest(W=0.7817826867103577, p_value=0.04004703089594841)
Variable is categorical: drug
Variable has two categories: drug
Equal variance: drug, wedsBDI

***Test results:
name = Pointbiserial Correlation
test_statistic = 0.53028
p_value = 0.64417
adjusted_p_value = 0.64417
alpha = 0.01
Null hypothesis = There is no association between Ecstasy and Alcohol.
Interpretation = Fail to reject the null hypothesis at alpha = 0.01. There is no association between Ecstasy and Alcohol.

Test: mannwhitney_u
***Test assumptions:
Exactly one explanatory variable: drug
Exactly one explained variable: wedsBDI
Independent (not paired) observations: drug
Variable is categorical: drug
Variable has two categories: drug
Continuous OR ORDINAL (not nominal) data: wedsBDI

***Test results:
name = Mann Whitney U Test
test_statistic = 8.00000
p_value = 0.18404
adjusted_p_value = 0.09202
alpha = 0.01
dof = 3
Effect size:
A12 = 0.88889
Null hypothesis = There is no difference in medians between drug = Ecstasy and drug = Alcohol on wedsBDI.
Interpretation = t(3) = 8.00000, p = 0.09202. Fail to reject the null hypothesis at alpha = 0.01. There is no difference in medians between drug = Ecstasy and drug = Alcohol on wedsBDI.The effect size is A12 = 0.88889. The effect size is the magnitude of the difference, which gives a holistic view of the results [1].
[1] Sullivan, G. M., & Feinn, R. (2012). Using effect size—or why the P value is not enough. Journal of graduate medical education, 4(3), 279-282.

Test: kruskall_wallis
***Test assumptions:
Independent (not paired) observations: drug
Exactly one explanatory variable: drug
Exactly one explained variable: wedsBDI
Continuous (not categorical) data: wedsBDI
Variable is categorical: drug
Variable has two or more categories: drug

***Test results:
name = Kruskall Wallis
test_statistic = 2.40196
p_value = 0.12118
adjusted_p_value = 0.12118
alpha = 0.01
dof = 3
Null hypothesis = There is no difference in medians between drug = Ecstasy, Alcohol on wedsBDI.
Interpretation = t(3) = 2.40196, p = 0.12118. Fail to reject the null hypothesis at alpha = 0.01. There is no difference in medians between drug = Ecstasy, Alcohol on wedsBDI.


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
