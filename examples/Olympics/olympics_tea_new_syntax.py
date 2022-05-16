import tea
import pandas as pd

''' 
Want to see if Wrestling is correlated with greater athlete Weight
than Swimming, and if Female athletes have a lower Weight than 
Male athletes.
'''

data_path = "./athlete_events_cleaned_weight.csv"

df = pd.read_csv(data_path)
id = tea.Unit('ID')
sport = id.nominal('Sport', categories=['Swimming', 'Wrestling'])
sex = id.nominal('Sex', categories=['M', 'F'])
weight = id.ratio('Weight')

tea.data(data_path, id)
tea.define_observational_study(contributor_variables=[sport, sex], outcome_variables=[weight])
tea.assume(groups_normally_distributed =[['Sport', 'Weight']], false_positive_error_rate=0.05)
tea.hypothesize(weight, [sport['Wrestling'].greaterThan(sport['Swimming'])])
tea.hypothesize(weight, [sex['F'].lessThan(sex['M'])])


'''
Results:
--------------
Test: mannwhitney_u
***Test assumptions:
Exactly one explanatory variable: Sex
Exactly one explained variable: Weight
Independent (not paired) observations: Sex
Variable is categorical: Sport
Variable has two categories: Sport
Continuous OR ORDINAL (not nominal) data: Weight

***Test results:
name = Mann Whitney U Test
test_statistic = 11876698893.00000
alpha = 0.05
dof = 196594
Effect size:
A12 = 0.17880
Null hypothesis = There is no difference in medians between Sex = M and Sex = F on Weight.
Interpretation = t(196594) = 11876698893.00000, p = 0.00000. Fail to reject the null hypothesis at alpha = 0.05. There is no difference in medians between Sex = M and Sex = F on Weight.The effect size is A12 = 0.17880. The effect size is the magnitude of the difference, which gives a holistic view of the results [1].
[1] Sullivan, G. M., & Feinn, R. (2012). Using effect size—or why the P value is not enough. Journal of graduate medical education, 4(3), 279-282.
'''
