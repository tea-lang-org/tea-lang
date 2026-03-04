"""No prediction — chi-square (unchanged syntax).

When you have no directional hypothesis, just omit predictions.
This works the same with both the string and structured API.

Expected outcome: Chi-square, Fisher's exact test

Run:  poetry run python examples/09_no_prediction.py
"""
import os
import tea

data_path = os.path.join(os.path.dirname(__file__), '..', 'tests', 'data', 'catsData.csv')

tea.data(data_path)
tea.define_variables([
    {'name': 'Training', 'data type': 'nominal', 'categories': ['Food as Reward', 'Affection as Reward']},
    {'name': 'Dance', 'data type': 'nominal', 'categories': ['Yes', 'No']},
])
tea.define_study_design({
    'study type': 'observational study',
    'contributor variables': 'Training',
    'outcome variables': 'Dance',
})
tea.assume({'Type I (False Positive) Error Rate': 0.05})

results = tea.hypothesize(['Training', 'Dance'])
