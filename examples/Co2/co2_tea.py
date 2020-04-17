import tea

data_path = "./co2.csv"

variables = [
    {
        'name' : 'id',
        'data type' : 'ratio'
    },
    {
        'name' : 'Plant',
        'data type': 'nominal',
        'categories': ['Qn1', 'Qn2', 'Qn3', 'Qc1', 'Qc2', 'Qc3']
    },
    {
        'name' : 'uptake',
        'data type' : 'ratio'
    }
]

tea.data(data_path, key='Id')
tea.define_variables(variables)

assumptions = {
    'Type I (False Positive) Error Rate': 0.05,
}

tea.assume(assumptions)

study_design = {
                        'study type': 'observational study',
                        'contributor variables': 'Plant',
                        'outcome variables': 'uptake'
                    }
tea.define_study_design(study_design)

tea.hypothesize(['Plant', 'uptake'], ['Plant: Qn1 < Qn2', 'Plant: Qc2 < Qc3'])
