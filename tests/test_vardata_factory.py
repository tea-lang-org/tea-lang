from tea.helpers.study_type_determiner import StudyTypeDeterminer
from tea.helpers.constants.default_values import DEFAULT_ALPHA_PARAMETER
from tea.runtimeDataStructures.resultData import ResultData
from tea.global_vals import observational_identifier
from tea.runtimeDataStructures.varData import VarData
from tea.ast import Literal, Node, Relate, Variable
from tea.runtimeDataStructures.bivariateData import BivariateData
from tea.runtimeDataStructures.dataset import Dataset
import unittest
from unittest import mock
from unittest.mock import Mock
import pandas as pd
from tea.vardata_factory import VarDataFactory
from unittest.mock import ANY


def create_mocked_study_function(value_to_return=None):
    def mocked_study_function(vars, design):
        return value_to_return
    return mocked_study_function


def create_assign_roles(value_to_return=None):
    def mocked_assign_roles(vars, study_type, design):
        return value_to_return
    return mocked_assign_roles


def create_add_paired_property(value_to_return=None):
    def mocked_add_paired_property(dataset, combined_data, study_type, design):
        return value_to_return
    return mocked_add_paired_property


def create_synthesize_tests(value_to_return=None):
    def mocked_synthesize_tests(dataset, assumptions, combined_data):
        return value_to_return
    return mocked_synthesize_tests


class VarDataFactoryTests(unittest.TestCase):
    def setUp(self):
        self.study_type_determiner_mock = Mock(spec=StudyTypeDeterminer)
        self.varadata_factory = VarDataFactory(self.study_type_determiner_mock)

    def test_vardata_created_for_variable(self):
        dataset = Mock(spec=Dataset)
        mocked_variable_data = {}
        dataset.get_variable_data.return_value = mocked_variable_data
        expression = Mock(spec=Variable)
        expression.name = ''

        # ACT
        returned_value = self.varadata_factory.create_vardata(dataset, expression, {})

        # ASSERT
        self.assertIsInstance(returned_value, VarData)

    def test_vardata_has_correct_metadata_for_variable(self):

        mocked_variable_data = {}
        mocked_expression_name = 'expr-name'

        dataset = Mock(spec=Dataset)
        dataset.get_variable_data.return_value = mocked_variable_data

        expression = Mock(spec=Variable)
        expression.name = mocked_expression_name

        # ACT
        returned_value = self.varadata_factory.create_vardata(dataset, expression, {})

        # ASSERT
        self.assertTrue('var_name' in returned_value.metadata)
        self.assertEqual(returned_value.metadata['var_name'], mocked_expression_name)

    def test_vardata_has_correct_metadata_for_literal(self):
        mocked_expression_value = 'expression value'
        data_for_dataset = [1, 2, 3]
        dataset = Mock(spec=Dataset)

        dataset.data = pd.Series(data_for_dataset)
        expression = Mock(spec=Literal)
        expression.value = mocked_expression_value

        # ACT
        returned_value = self.varadata_factory.create_vardata(dataset, expression, {})

        # ASSERT
        self.assertTrue('value' in returned_value.metadata)
        self.assertEqual(returned_value.metadata['value'], mocked_expression_value)
        self.assertEqual(len(returned_value.properties), len(data_for_dataset))

    def test_should_return_none_for_unknown_node(self):
        dataset = Mock(spec=Dataset)
        expression = Mock(spec=Node)

        # ACT
        returned_value = self.varadata_factory.create_vardata(dataset, expression, {})

        # ASSERT
        self.assertIsNone(returned_value)

    def test_bivariate_analysis_should_use_default_alpha_without_assumptions_called(self):
        data_for_dataset = [1, 2, 3]
        dataset = Mock(spec=Dataset)
        dataset.data = pd.Series(data_for_dataset)

        expression = Mock(spec=Relate)
        expression.vars = []
        expression.predictions = None
        mocked_role_1 = Mock()
        mocked_role_1.role = 'x'
        mocked_role_2 = Mock()
        mocked_role_2.role = 'x'

        result_data_mock = Mock(spec=ResultData)
        self.study_type_determiner_mock.determine_study_type = create_mocked_study_function(observational_identifier)

        with mock.patch('tea.vardata_factory.synthesize_tests', side_effect=create_synthesize_tests([])), \
                mock.patch('tea.vardata_factory.assign_roles', side_effect=create_assign_roles([mocked_role_1, mocked_role_2])), \
                mock.patch('tea.vardata_factory.ResultData', side_effect=lambda x, y: result_data_mock),\
                mock.patch('tea.vardata_factory.execute_test', side_effects=lambda x, y, z, a, b: []),\
                mock.patch('tea.vardata_factory.add_paired_property', side_effect=create_add_paired_property(None)) as mocked_add_paired_property:
            self.varadata_factory.create_vardata(dataset, expression, {})

            mocked_add_paired_property.assert_called_with(ANY, ANY, ANY, ANY)
            called_with = {type(arg): arg for arg in mocked_add_paired_property.call_args[0]}
            self.assertTrue(BivariateData in called_with)
            self.assertEqual(DEFAULT_ALPHA_PARAMETER, called_with[BivariateData].alpha)
