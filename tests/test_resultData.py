import pandas as pd

import tea
import os
import unittest 

from tea.logging import TeaLoggerConfiguration, TeaLogger
import logging
import altair as alt

from tea.runtimeDataStructures.resultData import ResultData
configuration = TeaLoggerConfiguration()
configuration.logging_level = logging.DEBUG
TeaLogger.initialize_logger(configuration)

base_url = 'https://homes.cs.washington.edu/~emjun/tea-lang/datasets/'
file_names = ['UScrime.csv', 'statex77.csv', 'catsData.csv', 'cholesterol.csv', 'soya.csv', 'co2.csv', 'exam.csv', 'liar.csv',
              'pbcorr.csv', 'spiderLong_within.csv', 'drug.csv', 'alcohol.csv', 'ecstasy.csv', 'gogglesData.csv', 'gogglesData_dummy.csv']
data_paths = [None] * len(file_names)


def load_data():
    global base_url, data_paths, file_names
    global drug_path

    for i in range(len(data_paths)):
        csv_name = file_names[i]

        csv_url = os.path.join(base_url, csv_name)
        data_paths[i] = tea.download_data(csv_url, csv_name)

def get_data_path(filename):
    load_data()
    try:
        data_idx = file_names.index(filename)
    except:
        raise ValueError(f"File is not found!:{filename}")
    data_path = data_paths[data_idx]

    return data_path

class ResultDataTests(unittest.TestCase):
    def test_result_data_correlations(self):
        data_path = get_data_path('statex77.csv')

        # Declare and annotate the variables of interest
        variables = [
            {
                'name': 'Illiteracy',
                'data type': 'interval',
                'categories': [0, 100]
            },
            {
                'name': 'Life Exp',
                'data type': 'ratio',
            }
        ]
        experimental_design = {
            'study type': 'observational study',
            'contributor variables': ['Illiteracy', 'Life Exp'],
            'outcome variables': ''
        }
        assumptions = {
            'Type I (False Positive) Error Rate': 0.05,
            'normal distribution': ['Illiteracy']
        }

        tea.data(data_path)
        tea.define_variables(variables)
        tea.define_study_design(experimental_design)
        tea.assume(assumptions, 'strict')

        results = tea.hypothesize(['Illiteracy', 'Life Exp'], [
                                'Illiteracy ~ Life Exp'])
        
        
        self.assertIsInstance(results, ResultData)
        self.assertEqual(len(results.test_to_results), 2)

        # Check Kendall's Tau 
        self.assertIn('kendalltau_corr', results.test_to_results.keys())
        kendalltau_corr_result = results.test_to_results['kendalltau_corr']
        chart = kendalltau_corr_result.generate_visualization()
        chart.show()
        self.assertIsNotNone(chart)
        self.assertIsInstance(chart, alt.Chart)
        print(kendalltau_corr_result.generate_template_text())
        # TODO: Add something in here to check more about the Chart internals
        # TODO: Could also print/display in an HTML to manually verify that the Chart is correct

        # Check Spearman's Rho
        spearman_corr_result = results.test_to_results['spearman_corr']
        chart = spearman_corr_result.generate_visualization()
        chart.show()
        self.assertIsNotNone(chart)
        self.assertIsInstance(chart, alt.Chart)
        print(spearman_corr_result.generate_template_text())

        # Check Pearson's Correlation 
        # TODO: Modify input data so that pearson_corr is selected. Currently, only spearman and kendall are 
        # print(results.test_to_results)
        # pearson_corr_result = results.test_to_results['pearson_corr']
        # chart = pearson_corr_result.generate_visualization()
        # chart.show()
        # self.assertIsNotNone(chart)
        # self.assertIsInstance(chart, alt.Chart)
        # print(pearson_corr_result.generate_template_text())

    def test_result_data_t_tests(self):
        raise NotImplementedError

    def test_output_builder(self): 
        raise NotImplementedError

    def test_output_formatter(self): 
        raise NotImplementedError