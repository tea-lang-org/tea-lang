"""Independent t-test — group comparison with integer categories.

String syntax:      tea.hypothesize(['So', 'Prob'], ['So:1 > 0'])
Structured syntax:  tea.hypothesize(['So', 'Prob'], [tea.compare(1, '>', 0)])

Expected outcome: Welch's t-test, Mann-Whitney U, Kruskal-Wallis

Run:  poetry run python examples/02_indep_t_test.py
"""
import os
import tea

data_path = os.path.join(os.path.dirname(__file__), '..', 'tests', 'data', 'UScrime.csv')

tea.data(data_path)
tea.define_variables([
    {'name': 'So', 'data type': 'nominal', 'categories': [0, 1]},
    {'name': 'Prob', 'data type': 'ratio', 'range': [0, 1]},
])
tea.define_study_design({
    'study type': 'observational study',
    'contributor variables': 'So',
    'outcome variables': 'Prob',
})
tea.assume({
    'Type I (False Positive) Error Rate': 0.05,
    'groups normally distributed': [['Prob', 'So']],
})

results = tea.hypothesize(['So', 'Prob'], [tea.compare(1, '>', 0)])
