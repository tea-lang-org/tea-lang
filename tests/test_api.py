from tea.ast import DataType
import tea.api
from tea.api import hypothesize
import unittest
from importlib import reload
from tea.variable import Ratio, Nominal, Ordinal, Interval
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

def unit_test_case():
    data_path = get_data_path('drug.csv')
    sno = tea.Unit("")
    drug = sno.nominal('drug', ['Ecstasy', 'Alcohol'])
    sundaybdi = sno.ratio('sundayBDI')
    wedsbdi = sno.ratio('wedsBDI')
    BDIchange = sno.interval('BDIchange')
    tea.data(data_path, key=sno)
    tea.define_observational_study([drug, sundaybdi],[BDIchange, wedsbdi] )
    tea.assume(false_positive_error_rate=0.05)
    
    tea.hypothesize([drug, wedsbdi], [drug['Ecstasy'].greaterThan(drug['Alcohol'])])

def unitless_test_case():
    data_path = get_data_path('drug.csv')
    drug = Nominal('drug', ['Ecstasy', 'Alcohol'])
    sundaybdi = Ratio('sundayBDI')
    wedsbdi = Ratio('wedsBDI')
    BDIchange = Interval('BDIchange')
    tea.data(data_path)
    tea.define_observational_study([drug, sundaybdi],[BDIchange, wedsbdi] )
    tea.assume(false_positive_error_rate=0.05)

    tea.hypothesize([sundaybdi, BDIchange], [sundaybdi.linearRelationship(BDIchange)])

class ApiTests(unittest.TestCase):

    def setUp(self):
        reload(tea.api)

    def test_define_variables_should_give_correct_length_with_unit(self):
        # ASSERT WITH UNIT
        unit_test_case()
        from tea.api import vars_objs as vars_to_test
        self.assertEqual(len(vars_to_test), 2)
    
    def test_define_variables_should_give_correct_length_without_unit(self):
        # ASSERT WITH UNIT
        unitless_test_case()
        from tea.api import vars_objs as vars_to_test
        self.assertEqual(len(vars_to_test), 2)

    def test_vars_objs_should_be_empty_before_defining(self):
        from tea.api import vars_objs as vars_to_test
        self.assertEqual(len(vars_to_test), 0)

    def test_define_variables_should_have_correct_names_with_unit(self):
        expected_names = ['drug', 'wedsBDI']

        # ACT
        unit_test_case()
        from tea.api import vars_objs as vars_to_test
        real_names = [var.name for var in vars_to_test]

        # ASSERT
        self.assertCountEqual(real_names, expected_names)
    
    def test_define_variables_should_have_correct_names_without_unit(self):
        expected_names = ['sundayBDI', 'BDIchange']

        # ACT
        unitless_test_case()
        from tea.api import vars_objs as vars_to_test
        real_names = [var.name for var in vars_to_test]

        # ASSERT
        self.assertCountEqual(real_names, expected_names)

    # Define variables using new api/syntax. Call hypothesis, then check var_objs
    def test_define_variables_should_have_correct_types_with_unit(self):
        unit_test_case()
        from tea.api import vars_objs as vars_to_test

        self.assertEqual(vars_to_test[0].dtype.value, DataType.NOMINAL.value)  # NominalT
        self.assertEqual(vars_to_test[1].dtype.value,DataType.RATIO.value)  # RatioT

    def test_define_variables_should_have_correct_types_without_unit(self):
        unitless_test_case()
        from tea.api import vars_objs as vars_to_test

        self.assertEqual(vars_to_test[0].dtype.value, DataType.RATIO.value)  # NominalT
        self.assertEqual(vars_to_test[1].dtype.value,DataType.INTERVAL.value)  # RatioT



# class DataForTests:

#     variables_to_define = [
#         {
#             'name': 'RatioT',
#             'data type': 'ratio'
#         },
#         {
#             'name': 'NominalT',
#             'data type': 'nominal',
#             'categories': ['Nominal0']
#         },
#         {
#             'name': 'OrdinalT',
#             'data type': 'ordinal',
#             'categories': ['Ordinal1', 'Ordinal2', 'Ordinal3']
#         },
#         {
#             'name': 'IntervalT',
#             'data type': 'interval',
#         }
#     ]
