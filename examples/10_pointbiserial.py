"""Pointbiserial correlation — gender predicts time.

String syntax:      tea.hypothesize(['time', 'gender'], ['gender:1 > 0'])
Structured syntax:  tea.hypothesize(['time', 'gender'], [tea.compare(1, '>', 0)])

Expected outcome: Mann-Whitney U, Kruskal-Wallis

Run:  poetry run python examples/10_pointbiserial.py
"""
import os
import tea

data_path = os.path.join(os.path.dirname(__file__), '..', 'tests', 'data', 'pbcorr.csv')

tea.data(data_path)
tea.define_variables([
    {'name': 'time', 'data type': 'ratio'},
    {'name': 'gender', 'data type': 'nominal', 'categories': [0, 1]},
    {'name': 'recode', 'data type': 'nominal', 'categories': [0, 1]},
])
tea.define_study_design({
    'study type': 'observational study',
    'contributor variables': ['gender', 'recode'],
    'outcome variables': 'time',
})
tea.assume({'Type I (False Positive) Error Rate': 0.05})

results = tea.hypothesize(['time', 'gender'], [tea.compare(1, '>', 0)])
