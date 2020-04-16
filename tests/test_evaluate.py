from tea.runtimeDataStructures.varData import VarData
from tea.ast import Literal, Variable
from tea.runtimeDataStructures.dataset import Dataset
import unittest
from unittest.mock import Mock
import pandas as pd
from tea.evaluate import evaluate


class EvaluateTests(unittest.TestCase):

    def test_vardata_created_for_variable(self):
        dataset = Mock(spec=Dataset)
        mocked_variable_data = {}
        dataset.get_variable_data.return_value = mocked_variable_data
        expression = Mock(spec=Variable)
        expression.name = ''

        # ACT
        returned_value = evaluate(dataset, expression, {})

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
        returned_value = evaluate(dataset, expression, {})

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
        returned_value = evaluate(dataset, expression, {})

        # ASSERT
        self.assertTrue('value' in returned_value.metadata)
        self.assertEqual(returned_value.metadata['value'], mocked_expression_value)
        self.assertEqual(len(returned_value.properties), len(data_for_dataset))
