import pandas as pd

import tea
import os

from tea.logging import TeaLoggerConfiguration, TeaLogger
import logging
configuration = TeaLoggerConfiguration()
configuration.logging_level = logging.DEBUG
TeaLogger.initialize_logger(configuration)

# This example is adapted from http://www.real-statistics.com/non-parametric-tests/wilcoxon-rank-sum-test/wilcoxon-rank-sum-exact-test/
def test_mann_whitney_0():
    tea.data('./tests/data/real_stats_3.csv')

    variables = [
        {
            'name': 'Treatment',
            'data type': 'nominal',
            'categories': ['Control', 'Drug']
        },
        {
            'name': 'Score',
            'data type': 'ratio'
        }
    ]
    experimental_design = {
        'study type': 'experiment',
        'independent variables': 'Treatment',
        'dependent variables': 'Score'
    }
    assumptions = {
        'Type I (False Positive) Error Rate': 0.05
    }


    tea.define_variables(variables)
    # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    tea.define_study_design(experimental_design)
    tea.assume(assumptions)
    tea.hypothesize(['Treatment', 'Score'], ['Treatment:Control != Drug'])