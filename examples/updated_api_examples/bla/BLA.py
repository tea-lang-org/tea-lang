# https://drive.google.com/drive/u/3/search?q=paper234
# Drunk User Interfaces: Determining Blood Alcohol Levels

import tea
data = './BLA.csv'

task = tea.Nominal('task', categories=["T", "S", "BHR", "SR", "CR"])
trial1 = tea.Ratio('Trial_1')
trial2 = tea.Ratio('Trial_2')
trial3 = tea.Ratio('Trial_3')
trial4 = tea.Ratio('Trial_4')
trial5 = tea.Ratio('Trial_5')

tea.data(data, key=task)
tea.define_experiment([task], [trial1, trial2, trial3, trial4, trial5])
tea.assume(false_positive_error_rate=0.05)

tea.hypothesize([task], [trial1.lessThan(trial5), trial2.lessThan(trial4)])


