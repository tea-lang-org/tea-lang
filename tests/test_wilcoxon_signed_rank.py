import pandas as pd

import tea
import os

from tea.logging import TeaLoggerConfiguration, TeaLogger
import logging
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

# This example is adapted from http://www.real-statistics.com/non-parametric-tests/wilcoxon-signed-ranks-test/
def test_wilcoxon_signed_rank_0():

    # variables = [
    #     {
    #         'name': 'Person',
    #         'data type': 'ratio'
    #     },
    #     {
    #         'name': 'Side',
    #         'data type': 'nominal',
    #         'categories': ['Right', 'Left']
    #     },
    #     {
    #         'name': 'Score',
    #         'data type': 'ratio'
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'experiment',
    #     'independent variables': 'Side',
    #     'dependent variables': 'Score',
    #     'within subjects': 'Side',
    #     # 'key': 'Person'
    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05
    # }

    person = tea.Unit('Person')
    side = person.nominal('Side', ['Right', 'Left'])
    score = person.numeric('Score')
    
    tea.data('./tests/data/real_stats_0.csv', key=person)
    tea.define_experiment([side], [score], within_subjects=[side])
    tea.assume(false_positive_error_rate=0.05)
    
    # tea.define_variables(variables)
    # # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions)

    # tea.hypothesize(['Side', 'Score'], ['Side:Right != Left'])
    tea.hypothesize([side, score], [side['Right'].notEquals(side['Left'])])


# This example is adapted from Example 1 on http://www.real-statistics.com/non-parametric-tests/wilcoxon-signed-ranks-test/
def test_wilcoxon_signed_rank_1():
    tea.data('./tests/data/real_stats_1.csv')

    # variables = [
    #     {
    #         'name': 'Subject',
    #         'data type': 'ratio'
    #     },
    #     {
    #         'name': 'Source',
    #         'data type': 'nominal',
    #         'categories': ['Memory', 'Median']
    #     },
    #     {
    #         'name': 'Score',
    #         'data type': 'ratio'
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'experiment',
    #     'independent variables': 'Source',
    #     'dependent variables': 'Score',
    #     'within subjects': 'Source'
    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05
    # }

    subject = tea.Numeric('Subject')
    source = tea.Nominal('Source', ['Memory', 'Median'])
    score = tea.Numeric('Score')

    tea.define_experiment([source], [score], within_subjects=[source])
    tea.assume(false_positive_error_rate=0.05)


    # tea.define_variables(variables)
    # # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions)

    # tea.hypothesize(['Source', 'Score'], ['Source:Memory != Median'])
    tea.hypothesize([source, score], [source['Memory'].notEquals(source['Median'])])


# This example is adapted from Example 2 on  http://www.real-statistics.com/non-parametric-tests/wilcoxon-signed-ranks-test/wilcoxon-signed-ranks-exact-test/
def test_wilcoxon_signed_rank_2():

    # variables = [
    #     {
    #         'name': 'Couple',
    #         'data type': 'ratio'
    #     },
    #     {
    #         'name': 'Person',
    #         'data type': 'nominal',
    #         'categories': ['Wife', 'Husband']
    #     },
    #     {
    #         'name': 'Score',
    #         'data type': 'ratio'
    #     }
    # ]
    # experimental_design = {
    #     'study type': 'observational study',
    #     'contributor variables': 'Person',
    #     'outcome variables': 'Score',
    #     'within subjects': 'Person'
    # }
    # assumptions = {
    #     'Type I (False Positive) Error Rate': 0.05
    # }

    couple = tea.Unit('Couple')
    person = couple.nominal('Person', ['Wife', 'Husband'])
    score = couple.numeric('Score')


    tea.data('./tests/data/real_stats_2.csv', key=couple)
    tea.define_observational_study([person], [score], within_subjects=[person])
    tea.assume(false_positive_error_rate=0.05)


    # tea.define_variables(variables)
    # # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    # tea.define_study_design(experimental_design)
    # tea.assume(assumptions)

    # tea.hypothesize(['Person', 'Score'], ['Person:Wife != Husband'])
    tea.hypothesize([person, score], [person['Wife'].notEquals(person['Husband'])])


    ## TODO: one-sided!