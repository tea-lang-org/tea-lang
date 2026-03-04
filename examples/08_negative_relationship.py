"""Negative relationship — inequality vs probability of imprisonment.

String syntax:      tea.hypothesize(['Ineq', 'Prob'], ['Ineq ~ -Prob'])
Structured syntax:  tea.hypothesize(['Ineq', 'Prob'], [tea.relationship('negative', 'Ineq', 'Prob')])

Expected outcome: Kendall's tau, Spearman's rho

Run:  poetry run python examples/08_negative_relationship.py
"""
import os
import tea

data_path = os.path.join(os.path.dirname(__file__), '..', 'tests', 'data', 'UScrime.csv')

tea.data(data_path)
tea.define_variables([
    {'name': 'So', 'data type': 'nominal', 'categories': [0, 1]},
    {'name': 'Prob', 'data type': 'ratio', 'range': [0, 1]},
    {'name': 'Ineq', 'data type': 'ratio'},
])
tea.define_study_design({
    'study type': 'observational study',
    'contributor variables': ['So', 'Prob'],
    'outcome variables': ['Prob', 'Ineq'],
})
tea.assume({'Type I (False Positive) Error Rate': 0.05})

results = tea.hypothesize(['Ineq', 'Prob'], [
    tea.relationship('negative', 'Ineq', 'Prob'),
])
