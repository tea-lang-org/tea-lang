import pandas as pd

import tea
import os
import unittest 

from tea.logging import TeaLoggerConfiguration, TeaLogger
import logging
configuration = TeaLoggerConfiguration()
configuration.logging_level = logging.DEBUG
TeaLogger.initialize_logger(configuration)

class InputDataTests(unittest.TestCase):
    def test_empty_file(self):
        # Read in CSV with only headers (no data)
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
        self.assertIsInstance(results, dict)
        # TODO: Check what the output dict looks like
