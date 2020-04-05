import numpy as np
import unittest
from tea.helpers.evaluateHelperMethods import compute_normal_distribution, is_numeric
from parameterized import parameterized
from tea.ast import DataType


class EvaluateHelperMethodsTests(unittest.TestCase):
    def test_compute_normal_distribution(self):
        np.random.seed(0)
        data = [3.03319599, -1.9392511,  5.19637956,  4.93035686,  6.67777232, 3.33221652,  4.48231727,
                5.7451167,  1.74927197, -1.13835557,  4.71136013,  0.94368067, 3.45836918,
                4.80279979,  6.41550484, 5.19735433,  3.68366857,  5.19261866, 6.08280386,
                1.21590325,  4.67839939, 2.15511797,  8.16360168,  4.04091618, 6.77094548]
        returned_value = compute_normal_distribution(data)
        self.assertAlmostEqual(0.2147399485, returned_value.p_value, 10)
        self.assertAlmostEqual(0.9470322132, returned_value.W, 10)

    @parameterized.expand([
        [DataType.INTERVAL, True],
        [DataType.RATIO, True],
        [DataType.ORDINAL, False],
        [DataType.NOMINAL, False],
    ])
    def test_is_numeric(self, type_to_check: DataType, expected: bool):
        self.assertEqual(is_numeric(type_to_check), expected)
