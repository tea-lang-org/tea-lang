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


class VariableInformation:
    """Class for keeping track of information about a variable."""

    def __init__(self, has_independent_samples, is_normal, sample_size, is_independent_variable=False,
                 variance=-1, is_continuous=False, is_categorical=False, number_of_categories=-1):
        self.has_independent_samples = has_independent_samples
        self.is_normal = is_normal # Does normality make sense for categorical variable?
        self.is_continuous = is_continuous
        self.is_categorical = is_categorical
        self.sample_size = sample_size
        self.is_independent_variable = is_independent_variable  # Assumes only independent or dependent variables.
        self.is_dependent_variable = not is_independent_variable

        if is_continuous:
            assert variance > 0, "Variance must be positive for a continuous variable."
        self.variance = variance

        if is_categorical:
            assert number_of_categories > 0, "Number of categories must be specified for categorical variables."
        self.number_of_categories = number_of_categories


class BivariateTestInformation:
    """Class for keeping track of information between variables for a bivariate test."""

    def __init__(self, variables: List[VariableInformation], is_bivariate_normal: bool = False,
                 difference_between_paired_values_is_normal: bool = False, similar_variances: bool = False,
                 paired_observations: bool = False):
        assert len(variables) == 2, "Only bivariate tests are supported."

        self.variables = variables
        self.first_variable = variables[0]
        self.second_variable = variables[1]

        if variables[0].is_independent_variable:
            self.independent_variable = variables[0]
        elif variables[1].is_independent_variable:
            self.independent_variable = variables[1]
        else:
            self.independent_variable = None

        # Can bivariate test have multiple dependent variables?
        if variables[0].is_dependent_variable and not variables[1].is_dependent_variable:
            self.dependent_variable = variables[0]
        elif variables[1].is_dependent_variable and not variables[0].is_dependent_variable:
            self.dependent_variable = variables[1]
        else:
            self.dependent_variable = None

        self.is_bivariate_normal = is_bivariate_normal
        self.difference_between_paired_values_is_normal = difference_between_paired_values_is_normal
        self.tests_have_similar_variances = similar_variances
        self.paired_observations = paired_observations

    @property
    def all_variables_have_independent_observations(self):
        return self.first_variable.has_independent_samples and self.second_variable.has_independent_samples

    @property
    def all_variables_are_continuous(self):
        return self.first_variable.is_continuous and self.second_variable.is_continuous

    @property
    def all_variables_are_categorical(self):
        return self.first_variable.is_categorical and self.second_variable.is_categorical

    @property
    def all_variables_are_normal(self):
        return self.first_variable.is_normal and self.second_variable.is_normal

    @property
    def all_variables_have_enough_samples(self):
        return self.first_variable.sample_size >= 30 and self.second_variable.sample_size >= 30

    @property
    def all_variables_have_enough_categories(self):
        return self.all_variables_are_categorical and \
               self.first_variable.number_of_categories >= 2 and \
               self.second_variable.number_of_categories >= 2


def find_applicable_bivariate_tests(test_information: BivariateTestInformation):
    def bool_val(cond):
        return BoolVal(True) if cond else BoolVal(False)

    students_t, chi_square = Bools('students_t chi_square')

    max_sat = Optimize()
    max_sat.add(students_t == And(bool_val(test_information.all_variables_have_independent_observations),
                                  bool_val(test_information.all_variables_are_normal),
                                  bool_val(test_information.all_variables_are_continuous),
                                  bool_val(test_information.tests_have_similar_variances)))

    max_sat.add(chi_square == And(bool_val(test_information.all_variables_have_independent_observations),
                                  bool_val(test_information.all_variables_are_categorical),
                                  bool_val(test_information.all_variables_have_enough_samples),
                                  bool_val(test_information.all_variables_have_enough_categories)))

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
normal_variable1 = VariableInformation(has_independent_samples =True, is_normal=True, variance=0.06, sample_size=35,
                                       is_continuous=True)
normal_variable2 = VariableInformation(has_independent_samples=True, is_normal=True, variance=0.06, sample_size=55,
                                       is_continuous=True)

normal_test_information = BivariateTestInformation(variables=[normal_variable1, normal_variable2],
                                                   similar_variances=True)

categorical_variable1 = VariableInformation(has_independent_samples=True, is_normal=False,
                                            is_categorical=True, sample_size=35, number_of_categories=2)
categorical_variable2 = VariableInformation(has_independent_samples=True, is_normal=False, is_categorical=True,
                                            sample_size=30, number_of_categories=5)

categorical_test_information = BivariateTestInformation(variables=[categorical_variable1, categorical_variable2])

print("Tests for normal samples: %s" % find_applicable_bivariate_tests(normal_test_information))
print("Tests for categorical samples: %s" % find_applicable_bivariate_tests(categorical_test_information))
