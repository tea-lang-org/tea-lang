import tea

tea.data("./UScrime.csv")
variables = [
    {
        'name' : 'So',
        'data type' : 'nominal',   # Options: 'nominal', 'ordinal', 'interval', 'ratio'
        'categories' : ['0', '1']
    },
    {
        'name' : 'Prob',
        'data type' : 'ratio',   # Options: 'nominal', 'ordinal', 'interval', 'ratio'
        # 'range' : [0,1]   # optional
    },
    {
        'name' : 'Ineq',
        'data type' : 'ordinal',   # Options: 'nominal', 'ordinal', 'interval', 'ratio'
        'categories': [28,29,30]
        # 'range' : [0,1]   # optional
    }
]

tea.define_variables(variables)

assumptions = {
    'log normal distribution': [['Ineq']],
    # 'equal variance': [['So', 'Ineq']],
    # 'groups normally distributed': [['So', 'Ineq']],
    'Type I (False Positive) Error Rate': 0.05,
}

tea.assume(assumptions, 'relaxed')

experimental_design = {
                        'study type': 'observational study',   # 'study type' could be 'experiment'
                        'contributor variables': 'So',   # 'experiment's have 'independent variables'
                        'outcome variables': 'Ineq',   # 'experiment's have 'dependent variables'
                    }
tea.define_study_design(experimental_design)

# tea.hypothesize(['So', 'Prob'], ['So:1 > 0'])
tea.hypothesize(['So', 'Ineq'], ['So:1 > 0'])
# tea.hypothesize(['Ineq', 'Prob'], ['Ineq ~ +Prob'])
