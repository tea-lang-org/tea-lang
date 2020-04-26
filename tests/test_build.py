from tea.ast import NegativeRelationship, PositiveRelationship
import unittest
from unittest.mock import Mock
from tea.build import create_prediction


class CreatePredictionTests(unittest.TestCase):
    def test_positive_continuous_prediction_should_produce_correct_positive_relationship(self):
        prediction_type = 'continuous prediction'
        var_mock1 = Mock()
        var_mock1.name = 'Ineq'

        var_mock2 = Mock()
        var_mock2.name = 'Prob'

        vars = [var_mock1, var_mock2]
        prediction = 'Ineq ~ +Prob'
        z = create_prediction(prediction_type, vars, prediction)
        self.assertIsInstance(z, PositiveRelationship)
        self.assertEqual(z.lhs.var, var_mock1)
        self.assertEqual(z.rhs.var, var_mock2)

    def test_negative_continuous_prediction_should_produce_correct_negative_relationship(self):
        prediction_type = 'continuous prediction'
        var_mock1 = Mock()
        var_mock1.name = 'Ineq'

        var_mock2 = Mock()
        var_mock2.name = 'Prob'

        vars = [var_mock1, var_mock2]
        prediction = 'Ineq ~ -Prob'
        z = create_prediction(prediction_type, vars, prediction)
        self.assertIsInstance(z, NegativeRelationship)
        self.assertEqual(z.lhs.var, var_mock1)
        self.assertEqual(z.rhs.var, var_mock2)

