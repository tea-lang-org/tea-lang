"""Wilcoxon signed-rank — not-equal comparison.

String syntax:      tea.hypothesize(['day', 'value'], ['day:sundayBDI != wedsBDI'])
Structured syntax:  tea.hypothesize(['day', 'value'], [tea.compare('sundayBDI', '!=', 'wedsBDI')])

Expected outcome: Wilcoxon signed-rank test

Run:  poetry run python examples/04_wilcoxon.py
"""
import os
import tea

data_path = os.path.join(os.path.dirname(__file__), '..', 'tests', 'data', 'alcohol.csv')

tea.data(data_path)
tea.define_variables([
    {'name': 'drug', 'data type': 'nominal', 'categories': ['Alcohol']},
    {'name': 'day', 'data type': 'nominal', 'categories': ['sundayBDI', 'wedsBDI']},
    {'name': 'value', 'data type': 'ratio'},
])
tea.define_study_design({
    'study type': 'experiment',
    'independent variables': 'day',
    'dependent variables': 'value',
    'within subjects': 'day',
})
tea.assume({'Type I (False Positive) Error Rate': 0.05})

results = tea.hypothesize(['day', 'value'], [tea.compare('sundayBDI', '!=', 'wedsBDI')])
