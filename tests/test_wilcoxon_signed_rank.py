import pandas as pd

import tea
import os

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

def test_wilcoxon_signed_rank():
    data_path = get_data_path('alcohol.csv')

    # Declare and annotate the variables of interest
    variables = [
        {
            'name': 'drug',
            'data type': 'nominal',
            'categories': ['Alcohol']
        },
        {
            'name': 'day',
            'data type': 'nominal',
            'categories': ['sundayBDI', 'wedsBDI']
        },
        {
            'name': 'value',
            'data type': 'ratio'
        }
    ]
    experimental_design = {
        'study type': 'experiment',
        'independent variables': 'day',
        'dependent variables': 'value',
        'within subjects': 'day'

    }
    assumptions = {
        'Type I (False Positive) Error Rate': 0.05
    }

    tea.data(data_path)
    tea.define_variables(variables)
    # Allows for using multiple study designs for the same dataset (could lead to phishing but also practical for saving analyses and reusing as many parts of analyses as possible)
    tea.define_study_design(experimental_design)
    tea.assume(assumptions)

    tea.hypothesize(['day', 'value'], ['day:sundayBDI != wedsBDI'])
    # print("\nfrom Field et al.")
    # print("Expected outcome: Wilcoxon signed rank test")
    print('++++++++++++')

    # TODO: Add a new test where there is a difference btw signed and not signed