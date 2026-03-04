"""Spearman correlation — single ordinal comparison.

String syntax:      tea.hypothesize(['Position', 'Creativity'], ['Position:1 > 6'])
Structured syntax:  tea.hypothesize(['Position', 'Creativity'], [tea.compare(1, '>', 6)])

Expected outcome: Kendall's tau, Spearman's rho

Run:  poetry run python examples/11_spearman.py
"""
import os
import tea

data_path = os.path.join(os.path.dirname(__file__), '..', 'tests', 'data', 'liar.csv')

tea.data(data_path)
tea.define_variables([
    {'name': 'Creativity', 'data type': 'interval'},
    {'name': 'Position', 'data type': 'ordinal', 'categories': [6, 5, 4, 3, 2, 1]},
    {'name': 'Novice', 'data type': 'nominal', 'categories': [0, 1]},
])
tea.define_study_design({
    'study type': 'observational study',
    'contributor variables': ['Novice', 'Creativity'],
    'outcome variables': 'Position',
})
tea.assume({'Type I (False Positive) Error Rate': 0.05})

results = tea.hypothesize(['Position', 'Creativity'], [tea.compare(1, '>', 6)])
