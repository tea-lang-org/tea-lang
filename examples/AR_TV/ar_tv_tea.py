import tea


data_path = "./ar_tv_long.csv"

# Declare and annotate the variables of interest
variables = [
    {
        'name' : 'ID',
        'data type' : 'ratio'
    },
    {
        'name' : 'Condition',
        'data type' : 'nominal',
        'categories' : ['AR', 'TV']
    },
    {
        'name' : 'Score',
        # 'data type' : 'ratio'
        'data type' : 'ordinal',
        'categories' : [1,2,3,4,5]
    }
]
experimental_design = {
                        'study type': 'experiment',
                        'independent variables': 'Condition',
                        'dependent variables': 'Score'
                    }
assumptions = {
    'Type I (False Positive) Error Rate': 0.05,
}

tea.data(data_path, key='ID')
tea.define_variables(variables)
tea.define_study_design(experimental_design)
tea.assume(assumptions)
results = tea.hypothesize(['Score', 'Condition'], ['Condition:AR > TV'])
print('++++++++++++')