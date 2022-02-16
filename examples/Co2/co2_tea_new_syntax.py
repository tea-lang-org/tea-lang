import tea
import pandas as pd
import tisane as ts

data_path = "./co2.csv"

df = pd.read_csv(data_path) #DF is never loaded -> Question: Where to load DF

id = ts.Unit('id') #Tisane unit lacks data type definitions
plant = id.nominal('Plant', categories=['Qn1', 'Qn2', 'Qn3', 'Qc1', 'Qc2', 'Qc3'])
uptake = id.numeric('uptake')

tea.define_observational_study(contributor_variables=[plant], outcome_variables=[uptake])

tea.assumption(type_I_error_rate=0.05)

hyp_1 = (uptake, plant['Qn1'].lessThan(plant['Qc2']))
hyp_2 = (uptake, plant['Qn2'].lessThan(plant['Qc3']))

tea.hypothesis([hyp_1, hyp_2])


'''
Results:
--------------
Test: kruskall_wallis
***Test assumptions:
Independent (not paired) observations: Plant
Exactly one explanatory variable: Plant
Exactly one explained variable: uptake
Continuous (not categorical) data: uptake
Variable is categorical: Plant
Variable has two or more categories: Plant

***Test results:
name = Kruskall Wallis
test_statistic = 6.89813
p_value = 0.22833
adjusted_p_value = 0.22833
alpha = 0.05
dof = 7
Null hypothesis = There is no difference in medians between Plant = Qn1, Qn2, Qn3, Qc1, Qc2, Qc3 on uptake.
Interpretation = t(7) = 6.89813, p = 0.22833. Fail to reject the null hypothesis at alpha = 0.05. There is no difference in medians between Plant = Qn1, Qn2, Qn3, Qc1, Qc2, Qc3 on uptake.
'''
