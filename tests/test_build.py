from tea.ast import NegativeRelationship, PositiveRelationship
import unittest
from unittest.mock import Mock
from tea.build import create_prediction
from parameterized import parameterized


class CreatePredictionTests(unittest.TestCase):

    @parameterized.expand([
        [' ~ +', PositiveRelationship],  # Var_1 ~ +Var_2
        [' ~ ', PositiveRelationship],  # Var_1 ~ Var_2
        [' ~ +', PositiveRelationship, '+'],  # +Var_1 ~ +Var_2
        [' ~ ', PositiveRelationship, '+'],  # +Var_1 ~ +Var_2

        [' ~ -', NegativeRelationship],  # Var_1 ~ -Var_2
        [' ~ ', NegativeRelationship, '-'],  # -Var_1 ~ Var_2
        [' ~ -', NegativeRelationship, '+'],  # +Var_1 ~ -Var_2
        [' ~ +', NegativeRelationship, '-'],  # -Var_1 ~ +Var_2
    ])
    def test_continuous_prediction_should_produce_correct_relationship(self, relation, expected_relationship_type, first_variable_prefix=''):
        prediction_type = 'continuous prediction'
        variable_1_name = 'Var_1'
        variable_2_name = 'Var_2'

        var_mock1 = Mock()
        var_mock1.name = variable_1_name

        var_mock2 = Mock()
        var_mock2.name = variable_2_name

        vars = [var_mock1, var_mock2]
        prediction = f'{first_variable_prefix}{variable_1_name}{relation}{variable_2_name}'
        z = create_prediction(prediction_type, vars, prediction)
        self.assertIsInstance(z, expected_relationship_type)
        self.assertEqual(z.lhs.var, var_mock1)
        self.assertEqual(z.rhs.var, var_mock2)
