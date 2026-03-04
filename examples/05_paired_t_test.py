"""Paired t-test — within-subjects string category comparison.

String syntax:      tea.hypothesize(['Group', 'Anxiety'], ['Group:Real Spider > Picture'])
Structured syntax:  tea.hypothesize(['Group', 'Anxiety'], [tea.compare('Real Spider', '>', 'Picture')])

Expected outcome: Paired Student's t-test, Wilcoxon signed-rank

Run:  poetry run python examples/05_paired_t_test.py
"""
import os
import tea

data_path = os.path.join(os.path.dirname(__file__), '..', 'tests', 'data', 'spiderLong_within.csv')

tea.data(data_path, key='id')
tea.define_variables([
    {'name': 'Group', 'data type': 'nominal', 'categories': ['Picture', 'Real Spider']},
    {'name': 'Anxiety', 'data type': 'ratio'},
])
tea.define_study_design({
    'study type': 'experiment',
    'independent variables': 'Group',
    'dependent variables': 'Anxiety',
    'within subjects': 'Group',
})
tea.assume({'Type I (False Positive) Error Rate': 0.05})

results = tea.hypothesize(['Group', 'Anxiety'], [tea.compare('Real Spider', '>', 'Picture')])
