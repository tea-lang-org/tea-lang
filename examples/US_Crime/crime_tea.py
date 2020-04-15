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
    # 'log normal distribution': [['Ineq']],
    # 'equal variance': [['So', 'Ineq']],
    # 'groups normally distributed': [['So', 'Ineq']],
    'Type I (False Positive) Error Rate': 0.05,
}

tea.assume(assumptions)

experimental_design = {
                        'study type': 'observational study',   # 'study type' could be 'experiment'
                        'contributor variables': 'Prob',   # 'experiment's have 'independent variables'
                        'outcome variables': 'Ineq',   # 'experiment's have 'dependent variables'
                    }
tea.define_study_design(experimental_design)

# tea.hypothesize(['So', 'Prob'], ['So:1 > 0'])
# tea.hypothesize(['So', 'Ineq'], ['So:1 > 0'])
tea.hypothesize(['Ineq', 'Prob'], ['Ineq ~ +Prob'])
