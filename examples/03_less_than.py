"""Less-than comparison — Olympics athlete weight by sex.

String syntax:      tea.hypothesize(['Sex', 'Weight'], ['Sex:F < M'])
Structured syntax:  tea.hypothesize(['Sex', 'Weight'], [tea.compare('F', '<', 'M')])

Expected outcome: Mann-Whitney U, Kruskal-Wallis

Run:  poetry run python examples/03_less_than.py
"""
import os
import tea

data_path = os.path.join(os.path.dirname(__file__), '..', 'tests', 'data', 'athlete_events_cleaned_weight.csv')

tea.data(data_path, key='ID')
tea.define_variables([
    {'name': 'ID', 'data type': 'ratio'},
    {'name': 'Sport', 'data type': 'nominal', 'categories': ['Swimming', 'Wrestling']},
    {'name': 'Sex', 'data type': 'nominal', 'categories': ['M', 'F']},
    {'name': 'Weight', 'data type': 'ratio'},
])
tea.define_study_design({
    'study type': 'observational study',
    'contributor variables': ['Sport', 'Sex'],
    'outcome variables': 'Weight',
})
tea.assume({
    'groups normally distributed': [['Sport', 'Weight']],
    'Type I (False Positive) Error Rate': 0.05,
})

results = tea.hypothesize(['Sex', 'Weight'], [tea.compare('F', '<', 'M')])
