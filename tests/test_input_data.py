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
    def test_empty_file(self):
        # Read in CSV with only headers (no data)
        # data_path = load_data_from_url("https://github.com/tea-lang-org/tea-lang/blob/master/tests/data/ar_tv_empty.csv", "ar_tv_empty.csv")
        data_path = "tests/data/ar_tv_empty.csv"

        # variables = [
        #     {
        #         'name': 'ID',
        #         'data type': 'ratio'
        #     },
        #     {
        #         'name': 'Condition',
        #         'data type': 'nominal',
        #         'categories': ['AR', 'TV']
        #     },
        #     {
        #         'name': 'Score',
        #         'data type': 'ordinal',
        #         'categories': [1,2,3,4,5]
        #     }
        # ]

        # experimental_design = {
        #     'study type': 'experiment',
        #     'independent variables': 'Condition',
        #     'dependent variables': 'Score'
        # }

        # assumptions = {
        #     'Type I (False Positive) Error Rate': 0.01969
        # }

        # tea.data(data_path, key='ID')
        # tea.define_variables(variables)
        # tea.define_study_design(experimental_design)
        # tea.assume(assumptions)
        # results = tea.hypothesize(['Score', 'Condition'], ['Condition:AR > TV'])

        id = tea.Unit('ID')
        condition = id.nominal('Condition', ['AR', 'TV'])
        score = id.ordinal('Score', [1,2,3,4,5])

        tea.data(data_path, key=id) 
        tea.define_experiment([condition], [score])
        tea.assume(false_positive_error_rate=0.01969)

        # New Tea Syntax
        results = tea.hypothesize([score, condition], [condition['AR'].greaterThan(condition['TV'])])

        self.assertIsNotNone(results)
        self.assertIsInstance(results, list)
        self.assertIn('mannwhitney_u', results)
