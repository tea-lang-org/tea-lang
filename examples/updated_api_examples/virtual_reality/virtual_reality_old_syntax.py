import tea
data_path = './vr_data.csv'

variables = [
    {
        'name': 'ID', 
        'data type': 'ratio'
    },
    {
        'name': 'Condition',
        'data type': 'nominal',
        'categories': ['FA', 'FNA', 'HA', 'HNA']
    },
    {
        'name': 'Emotion',
        'data type': 'ratio'
    },
    {
        'name': 'Agency',
        'data type': 'nominal',
        'categories': ['Y', 'N']
    }, 
    {
        'name': 'Presence',
        'data type': 'ratio'
    }
]

experimental_design = {
    'study type': 'experiment',
    'independent variables': ['Emotion', 'Agency'],
    'dependent variables': ['Condition', 'Presence']
}

assumptions = {
    'Type I (False Positive) Error Rate': 0.05
}
tea.data(data_path, key='ID')
tea.define_variables(variables)
tea.define_study_design(experimental_design)
tea.assume(assumptions)
results = tea.hypothesize(['Presence', 'Agency'], ['Agency:Y > N'])