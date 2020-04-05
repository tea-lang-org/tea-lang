from build.lib.tea.ast import DataType
import tea.api
from tea.api import define_variables
import unittest
from importlib import reload


class ApiTests(unittest.TestCase):

    def setUp(self):
        reload(tea.api)

    def test_define_variables_should_give_correct_length(self):
        define_variables(DataForTests.variables_to_define)

        # ASSERT
        from tea.api import vars_objs as vars_to_test
        self.assertEqual(len(vars_to_test), 4)

    def test_vars_objs_should_be_empty_before_defining(self):
        from tea.api import vars_objs as vars_to_test
        self.assertEqual(len(vars_to_test), 0)

    def test_define_variables_should_have_correct_names(self):
        expected_names = ['NominalT', 'IntervalT', 'OrdinalT', 'RatioT']

        # ACT
        define_variables(DataForTests.variables_to_define)
        from tea.api import vars_objs as vars_to_test
        real_names = [var.name for var in vars_to_test]

        # ASSERT
        self.assertCountEqual(real_names, expected_names)

    def test_define_variables_should_have_correct_types(self):

        define_variables(DataForTests.variables_to_define)
        from tea.api import vars_objs as vars_to_test
        sorted_vars = sorted(vars_to_test, key=lambda x: x.name)

        self.assertEqual(sorted_vars[0].dtype.value,
                         DataType.INTERVAL.value)  # IntervalT
        self.assertEqual(sorted_vars[1].dtype.value,
                         DataType.NOMINAL.value)  # NominalT
        self.assertEqual(sorted_vars[2].dtype.value,
                         DataType.ORDINAL.value)  # OrdinalT
        self.assertEqual(sorted_vars[3].dtype.value,
                         DataType.RATIO.value)  # RatioT


class DataForTests:

    variables_to_define = [
        {
            'name': 'RatioT',
            'data type': 'ratio'
        },
        {
            'name': 'NominalT',
            'data type': 'nominal',
            'categories': ['Nominal0']
        },
        {
            'name': 'OrdinalT',
            'data type': 'ordinal',
            'categories': ['Ordinal1', 'Ordinal2', 'Ordinal3']
        },
        {
            'name': 'IntervalT',
            'data type': 'interval',
        }
    ]
