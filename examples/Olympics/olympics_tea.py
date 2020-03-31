import tea

''' 
Want to see if Wrestling is correlated with greater athlete Weight
than Swimming.
'''

data_path = "./athlete_events.csv"

# Declare and annotate the variables of interest
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
        'name': 'Weight',
        # 'data type': 'ratio',
        # 'data type' : 'interval',
        # 'range': [20, 110]
        'data type' : 'ordinal',
        'categories' : [22,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106]
    }
]
experimental_design = {
    'study type': 'observational study',
    'contributor variables': 'Sport',
    'outcome variables': 'Weight',
}
assumptions = {
    'Type I (False Positive) Error Rate': 0.05,
}

tea.data(data_path, key='ID')
tea.define_variables(variables)
tea.define_study_design(experimental_design)
tea.assume(assumptions)
results = tea.hypothesize(['Sport', 'Weight'], ['Sport:Wrestling < Swimming'])
print('++++++++++++')
