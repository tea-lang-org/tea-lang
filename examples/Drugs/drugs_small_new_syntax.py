import tea
import pandas as pd

d = {'id': pd.Series([1,2,3,4,5,6],index=['0', '1', '2', '3', '4', '5']),
    'drug': pd.Series(["Ecstasy", "Ecstasy", "Ecstasy", "Alcohol", "Alcohol", "Alcohol"],
                       index=['0', '1', '2', '3', '4', '5']),
     'sundayBDI': pd.Series([15, 35, 16, 16, 15, 20], index=['0', '1', '2', '3', '4', '5']),
     'wedsBDI': pd.Series([28, 35, 35, 5, 6, 30], index=['0', '1', '2', '3', '4', '5']),
     'BDIchange': pd.Series([13, 0, 19, -11, -9, 10], index=['0', '1', '2', '3', '4', '5'])}

df = pd.DataFrame(d)

id = tea.Unit('id')
drug = id.nominal('drug', categories=['Ecstasy', 'Alcohol'])
sundayBDI = id.ratio('sundayBDI')
wedsBDI = id.ratio('wedsBDI')
BDIchange = id.ratio('BDIchange')

tea.data(df, id)

tea.define_observational_study([drug, sundayBDI],[BDIchange, wedsBDI] )
tea.assume(false_positive_error_rate=0.01)

tea.hypothesize([drug, wedsBDI], [drug['Ecstasy'].greaterThan(drug['Alcohol'])])
tea.hypothesize([sundayBDI, BDIchange], [sundayBDI.linearRelationship(BDIchange)])
