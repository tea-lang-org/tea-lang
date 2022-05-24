import pandas as pd

import tea
import os
import unittest 

from tea.build import load_data_from_url
from tea.logging import TeaLoggerConfiguration, TeaLogger
import logging
configuration = TeaLoggerConfiguration()
configuration.logging_level = logging.DEBUG
TeaLogger.initialize_logger(configuration)

class InputDataTests(unittest.TestCase):
    def test_empty_file_ar_tv(self):
        # Read in CSV with only headers (no data)
        # data_path = load_data_from_url("https://github.com/tea-lang-org/tea-lang/blob/master/tests/data/ar_tv_empty.csv", "ar_tv_empty.csv")
        data_path = "tests/data/ar_tv_empty.csv"

        variables = [
            {
                'name': 'ID',
                'data type': 'ratio'
            },
            {
                'name': 'Condition',
                'data type': 'nominal',
                'categories': ['AR', 'TV']
            },
            {
                'name': 'Score',
                'data type': 'ordinal',
                'categories': [1,2,3,4,5]
            }
        ]

        experimental_design = {
            'study type': 'experiment',
            'independent variables': 'Condition',
            'dependent variables': 'Score'
        }

        assumptions = {
            'Type I (False Positive) Error Rate': 0.01969
        }

        tea.data(data_path, key='ID')
        tea.define_variables(variables)
        tea.define_study_design(experimental_design)
        tea.assume(assumptions)
        results = tea.hypothesize(['Score', 'Condition'], ['Condition:AR > TV'])

        self.assertIsNotNone(results)
        self.assertIsInstance(results, list)
        self.assertIn('mannwhitney_u', results)
    
    def test_empty_file_vr(self):
        data_path = "tests/data/vr_empty.csv"

        variables = [
            {
                'name': 'ID', 
                'data type': 'ratio'
            },
            {
                'name': 'Condition',
                'data type': 'nominal',
                'categories': ['FA', 'FNA', 'HA', 'HNA']
            },
            {
                'name': 'Emotion',
                'data type': 'ratio'
            },
            {
                'name': 'Agency',
                'data type': 'nominal',
                'categories': ['Y', 'N']
            }, 
            {
                'name': 'Presence',
                'data type': 'ratio'
            }
        ]

        experimental_design = {
            'study type': 'experiment',
            'independent variables': ['Emotion', 'Agency'],
            'dependent variables': ['Condition', 'Presence']
        }

        assumptions = {
            'Type I (False Positive) Error Rate': 0.05
        }
        tea.data(data_path, key='ID')
        tea.define_variables(variables)
        tea.define_study_design(experimental_design)
        tea.assume(assumptions)
        results = tea.hypothesize(['Presence', 'Agency'], ['Agency:Y > N'])

        self.assertIsNotNone(results)
        self.assertIsInstance(results, list)