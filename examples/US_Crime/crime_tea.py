import tea

tea.data("https://homes.cs.washington.edu/~emjun/tea-lang/datasets/UScrime.csv")

variables = [
    {
        'name' : 'So',
        'data type' : 'nominal',
        'categories' : ['0', '1']
    },
    {
        'name' : 'Prob',
        'data type' : 'ratio',
        'range' : [0,1]   # optional
    },
    {
        'name' : 'Ineq',
        'data type' : 'ratio'
    }
]

tea.define_variables(variables)

assumptions = {
    # 'equal variance': [['So', 'Ineq']],
    # 'groups normally distributed': [['So', 'Prob']],
    'Type I (False Positive) Error Rate': 0.05,
}

tea.assume(assumptions)

study_design = {
                        'study type': 'observational study',
                        'contributor variables': ['So', 'Prob'],
                        'outcome variables': ['Prob', 'Ineq']
                }
tea.define_study_design(study_design)

# tea.hypothesize(['So', 'Ineq'], ['So:1 > 0'])
# tea.hypothesize(['So', 'Prob'], ['So:1 > 0'])
tea.hypothesize(['Ineq', 'Prob'], ['Ineq ~ -Prob'])
