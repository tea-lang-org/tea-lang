from enum import Flag, auto
from typing import List
from z3 import *


class Tests(Flag):
    NONE = 0
    STUDENTST = auto()
    CHISQUARE = auto()
    UTEST = auto()

    PARAMETRIC = STUDENTST
    NONPARAMETRIC = CHISQUARE | UTEST


class SampleInformation:
    """Class for keeping track of information about a sample."""

    def __init__(self, is_independent, is_normal, is_continuous, is_categorical, variance, sample_size,
                 number_of_categories=0):
        self.is_independent = is_independent
        self.is_normal = is_normal
        self.is_continuous = is_continuous
        self.is_categorical = is_categorical
        self.variance = variance
        self.sample_size = sample_size
        self.number_of_categories = number_of_categories


def find_applicable_tests(samples: List[SampleInformation], tests_with_small_variance_diffs: list):
    assert len(samples) == 2, "Only bivariate tests are currently supported."

    def gen_bool_val(cond):
        return BoolVal(True) if cond else BoolVal(False)

    def has_enough_categories(sample: SampleInformation):
        return sample.number_of_categories >= 2

    students_t, chi_square = Bools('students_t chi_square')

    test_has_independent_observations = []
    test_is_normal = []
    test_is_continuous = []
    test_is_categorical = []
    test_has_large_sample_size = []

    for sampleInformation in samples:
        test_has_independent_observations.append(gen_bool_val(sampleInformation.is_independent))
        test_is_normal.append(gen_bool_val(sampleInformation.is_normal))
        test_is_continuous.append(gen_bool_val(sampleInformation.is_continuous))
        test_is_categorical.append(gen_bool_val(sampleInformation.is_categorical))
        test_has_large_sample_size.append(gen_bool_val(sampleInformation.sample_size >= 30))

    tests_have_similar_variances = BoolVal(False) if not tests_with_small_variance_diffs else BoolVal(True)

    max_sat = Optimize()
    max_sat.add(students_t == And(test_has_independent_observations[0], test_has_independent_observations[1],
                                  test_is_normal[0], test_is_normal[1],
                                  test_is_continuous[0], test_is_continuous[1],
                                  tests_have_similar_variances))
    max_sat.add(chi_square == And(test_has_independent_observations[0], test_has_independent_observations[1],
                                  test_is_categorical[0], test_is_categorical[1],
                                  test_has_large_sample_size[0], test_has_large_sample_size[1],
                                  gen_bool_val(has_enough_categories(samples[0])), gen_bool_val(has_enough_categories(samples[1]))))

    max_sat.add_soft(students_t)
    max_sat.add_soft(chi_square)

    applicable_tests = Tests.NONE
    if max_sat.check() == sat:
        model = max_sat.model()
        if model[students_t]:
            applicable_tests |= Tests.STUDENTST
        if model[chi_square]:
            applicable_tests |= Tests.CHISQUARE

    return applicable_tests


# Test by creating some sample data.
normal_sample1 = SampleInformation(is_independent=True, is_normal=True, is_continuous=True, is_categorical=False, variance=0.06,
                            sample_size=35)
normal_sample2 = SampleInformation(is_independent=True, is_normal=True, is_continuous=True, is_categorical=False, variance=0.06,
                            sample_size=55)

categorical_sample1 = SampleInformation(is_independent=True, is_normal=False, is_continuous=False, is_categorical=True, variance=-1, sample_size=35, number_of_categories=2)
categorical_sample2 = SampleInformation(is_independent=True, is_normal=False, is_continuous=False, is_categorical=True, variance=-1, sample_size=30, number_of_categories=5)

print("Tests for normal samples: %s" % find_applicable_tests(samples=[normal_sample1, normal_sample2], tests_with_small_variance_diffs=[(0, 1)]))
print("Tests for categorical samples: %s" % find_applicable_tests(samples=[categorical_sample1, categorical_sample2], tests_with_small_variance_diffs=[(0, 1)]))
