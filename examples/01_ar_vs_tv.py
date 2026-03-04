"""AR vs TV experiment — group comparison with compare().

String syntax:      tea.hypothesize(['Score', 'Condition'], ['Condition:AR > TV'])
Structured syntax:  tea.hypothesize(['Score', 'Condition'], [tea.compare('AR', '>', 'TV')])

Expected outcome: Mann-Whitney U test

Run:  poetry run python examples/01_ar_vs_tv.py
"""
import os
import tea

data_path = os.path.join(os.path.dirname(__file__), '..', 'tests', 'data', 'ar_tv_long.csv')

tea.data(data_path, key='ID')
tea.define_variables([
    {'name': 'ID', 'data type': 'ratio'},
    {'name': 'Condition', 'data type': 'nominal', 'categories': ['AR', 'TV']},
    {'name': 'Score', 'data type': 'ordinal', 'categories': [1, 2, 3, 4, 5]},
])
tea.define_study_design({
    'study type': 'experiment',
    'independent variables': 'Condition',
    'dependent variables': 'Score',
})
tea.assume({'Type I (False Positive) Error Rate': 0.01969})

results = tea.hypothesize(['Score', 'Condition'], [tea.compare('AR', '>', 'TV')])
