"""Positive relationship — Pearson correlation.

String syntax:      tea.hypothesize(['Illiteracy', 'Life Exp'], ['Illiteracy ~ Life Exp'])
Structured syntax:  tea.hypothesize(['Illiteracy', 'Life Exp'], [tea.relationship('positive', 'Illiteracy', 'Life Exp')])

Expected outcome: Kendall's tau, Spearman's rho

Run:  poetry run python examples/07_positive_relationship.py
"""
import os
import tea

data_path = os.path.join(os.path.dirname(__file__), '..', 'tests', 'data', 'statex77.csv')

tea.data(data_path)
tea.define_variables([
    {'name': 'Illiteracy', 'data type': 'interval', 'categories': [0, 100]},
    {'name': 'Life Exp', 'data type': 'ratio'},
])
tea.define_study_design({
    'study type': 'observational study',
    'contributor variables': ['Illiteracy', 'Life Exp'],
    'outcome variables': '',
})
tea.assume({
    'Type I (False Positive) Error Rate': 0.05,
    'normal distribution': ['Illiteracy'],
}, 'strict')

results = tea.hypothesize(['Illiteracy', 'Life Exp'], [
    tea.relationship('positive', 'Illiteracy', 'Life Exp'),
])
