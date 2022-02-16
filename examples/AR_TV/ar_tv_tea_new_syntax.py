import tea

data_path = './ar_tv_long.csv'

id = tea.Unit('ID')
condition = id.nominal('Condition', ['AR', 'TV'])
score = id.ordinal('Score', [1,2,3,4,5])

tea.data(data_path, key='ID') # Change Data so that it knows to look by the Base Unit
tea.define_experiment([condition], [score])
tea.assume(false_positive_error_rate=0.01969)
results = tea.hypothesize(['Score', 'Condition'], ['Condition:AR > TV'])

