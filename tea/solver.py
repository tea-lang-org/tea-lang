from enum import Flag, auto
from typing import List
from z3 import *

from tea.evaluate_data_structures import CombinedData, VarData
from tea.evaluate_helper_methods import iv_identifier, dv_identifier


class Tests(Flag):
    NONE = 0
    STUDENTST = auto()
    CHISQUARE = auto()
    UTEST = auto()
    PEARSON_CORRELATION = auto()
    SPEARMAN_CORRELATION = auto()
    PAIRED_SAMPLES_TTEST = auto()
    WILCOXON_SIGN_RANK_TEST = auto()
    BINOMIAL_TEST = auto()

    PARAMETRIC = STUDENTST | PAIRED_SAMPLES_TTEST | PEARSON_CORRELATION
    NONPARAMETRIC = CHISQUARE | UTEST | SPEARMAN_CORRELATION | WILCOXON_SIGN_RANK_TEST


class Assumptions(Flag):
    NONE = 0
    INDEPENDENT_OBSERVATIONS = auto()
    NORMALLY_DISTRIBUTED_VARIABLES = auto()
    NORMALLY_DISTRIBUTED_DIFFERENCE_BETWEEN_VARIABLES = auto()
    SYMMETRICALLY_DISTRIBUTED_DIFFERENCE_BETWEEN_VARIABLES = auto()
    SIMILAR_VARIANCES = auto()
    LARGE_SAMPLE_SIZE = auto()
    VALUES_ARE_FREQUENCIES = auto()
    PAIRED_OBSERVATIONS = auto()
    NO_OUTLIERS = auto()
    NO_OUTLIERS_IN_DIFFERENCE_BETWEEN_VARIABLES = auto()
    LINEAR_RELATIONSHIP = auto()
    BIVARIATE_NORMAL_VARIABLES = auto()
    RELATED_SAMPLES = auto()
    MONOTONIC_RELATIONSHIP = auto()
    ALL_VARIABLES_CONTINUOUS_OR_ORDINAL = auto()
    DEPENDENT_VARIABLE_CONTINUOUS_OR_ORDINAL = auto()


def assumptions_for_test(test: Tests) -> Assumptions:
    assumptions = Assumptions.NONE

    if test & Tests.STUDENTST:
        # Really, just the 2 groups of the dependent variable must be normally distributed.
        assumptions |= Assumptions.INDEPENDENT_OBSERVATIONS \
                       | Assumptions.NORMALLY_DISTRIBUTED_VARIABLES \
                       | Assumptions.SIMILAR_VARIANCES \
                       | Assumptions.LARGE_SAMPLE_SIZE

    elif test & Tests.CHISQUARE:
        assumptions |= Assumptions.INDEPENDENT_OBSERVATIONS \
                       | Assumptions.LARGE_SAMPLE_SIZE \
                       | Assumptions.VALUES_ARE_FREQUENCIES

    elif test & Tests.UTEST:
        assumptions |= Assumptions.INDEPENDENT_OBSERVATIONS \
                       | Assumptions.SIMILAR_VARIANCES

    elif test & Tests.PEARSON_CORRELATION:
        assumptions |= Assumptions.INDEPENDENT_OBSERVATIONS \
                       | Assumptions.LINEAR_RELATIONSHIP \
                       | Assumptions.BIVARIATE_NORMAL_VARIABLES \
                       | Assumptions.NO_OUTLIERS

    elif test & Tests.PAIRED_SAMPLES_TTEST:
        assumptions |= Assumptions.RELATED_SAMPLES \
                       | Assumptions.INDEPENDENT_OBSERVATIONS \
                       | Assumptions.NORMALLY_DISTRIBUTED_DIFFERENCE_BETWEEN_VARIABLES \
                       | Assumptions.NO_OUTLIERS_IN_DIFFERENCE_BETWEEN_VARIABLES

    elif test & Tests.SPEARMAN_CORRELATION:
        assumptions |= Assumptions.MONOTONIC_RELATIONSHIP \
                        | Assumptions.ALL_VARIABLES_CONTINUOUS_OR_ORDINAL

    elif test & Tests.WILCOXON_SIGN_RANK_TEST:
        assumptions |= Assumptions.DEPENDENT_VARIABLE_CONTINUOUS_OR_ORDINAL \
                        | Assumptions.SYMMETRICALLY_DISTRIBUTED_DIFFERENCE_BETWEEN_VARIABLES

    elif test & Tests.BINOMIAL_TEST:
        assumptions |= Assumptions.INDEPENDENT_OBSERVATIONS

    else:
        assert 0, 'Test %s not supported.' % test

    return assumptions


class VariableInformation:
    """Class for keeping track of information about a variable."""

    def __init__(self, has_independent_samples, sample_size=-1, is_normal=None, is_independent_variable=False,
                 is_dependent_variable=False, variance=-1, is_continuous=False, is_categorical=False,
                 number_of_categories=-1, is_ordinal=False):
        self.has_independent_samples = has_independent_samples
        self.is_continuous = is_continuous
        self.is_categorical = is_categorical
        self.sample_size = sample_size
        self.is_independent_variable = is_independent_variable  # Assumes only independent or dependent variables.
        self.is_dependent_variable = is_dependent_variable
        self.is_ordinal = is_ordinal

        if is_continuous:
            assert variance > 0, "Variance must be positive for a continuous variable."
            assert is_normal is not None
        self.variance = variance
        self.is_normal = is_normal

        if is_categorical:
            assert number_of_categories > 0, "Number of categories must be specified for categorical variables."
        self.number_of_categories = number_of_categories


class BivariateTestInformation:
    """Class for keeping track of information between variables for a bivariate test."""

    def __init__(self, variables: List[VariableInformation], is_bivariate_normal: bool = False,
                 difference_between_paired_values_is_normal: bool = False, similar_variances: bool = False,
                 observations_are_paired: bool = False):
        assert len(variables) == 2, "Only bivariate tests are supported."

        self.variables = variables
        independent_variables = [variable for variable in variables if variable.is_independent_variable]
        assert len(independent_variables) <= 1, \
            "Only one independent variable expected instead of %d" % len(independent_variables)
        self.independent_variable = independent_variables[0] if len(independent_variables) else None

        dependent_variables = [variable for variable in variables if variable.is_dependent_variable]
        assert len(dependent_variables) <= 1, \
            "Only one dependent variable expected instead of %d" % len(dependent_variables)
        self.dependent_variable = dependent_variables[0] if len(dependent_variables) else None

        self.is_bivariate_normal = is_bivariate_normal
        self.difference_between_paired_values_is_normal = difference_between_paired_values_is_normal
        self.samples_have_similar_variances = similar_variances
        self.observations_are_paired = observations_are_paired

    @staticmethod
    def all_elements_satisfy_property(elements, check_property):
        return not next((element for element in elements if not check_property(element)), None)

    def all_variables_satisfy_property(self, check_property):
        return self.all_elements_satisfy_property(self.variables, check_property)

    @property
    def all_variables_have_independent_observations(self):
        return self.all_variables_satisfy_property(lambda var: var.has_independent_samples)

    @property
    def all_variables_are_continuous(self):
        return self.all_variables_satisfy_property(lambda var: var.is_continuous)

    @property
    def dependent_variable_is_continuous(self):
        return self.dependent_variable is not None and self.dependent_variable.is_continuous

    @property
    def dependent_variable_is_ordinal(self):
        return self.dependent_variable is not None and self.dependent_variable.is_ordinal

    @property
    def dependent_variable_is_categorical(self):
        return self.dependent_variable is not None and self.dependent_variable.is_categorical

    @property
    def independent_variable_is_continuous(self):
        return self.independent_variable is not None and self.independent_variable.is_continuous

    @property
    def all_variables_are_categorical(self):
        return self.all_variables_satisfy_property(lambda var: var.is_categorical)

    @property
    def independent_variable_is_categorical(self):
        return self.independent_variable is not None and self.independent_variable.is_categorical

    @property
    def all_variables_are_continuous_or_ordinal(self):
        return self.all_elements_satisfy_property(lambda var: var.is_continuous or var.is_ordinal)

    @property
    def all_variables_have_enough_samples(self):
        return self.all_variables_satisfy_property(lambda var: var.sample_size >= 30)

    @property
    def all_variables_have_enough_categories(self):
        return self.all_variables_are_categorical and \
               self.all_variables_satisfy_property(lambda var: var.number_of_categories >= 2)

    def dependent_variable_has_num_categories(self, num_categories):
        return self.dependent_variable_is_categorical and \
                self.dependent_variable.number_of_categories == num_categories

    @property
    def independent_variable_has_enough_categories(self):
        return self.independent_variable_is_categorical and self.independent_variable.number_of_categories >= 2

def get_independent_variable(data: CombinedData) -> VarData:
    independent_variables = data.get_vars(iv_identifier)
    assert len(independent_variables) <= 1, \
        "Only one independent variable expected instead of %d" % len(independent_variables)
    return independent_variables[0] if len(independent_variables) else None

def get_dependent_variable(data: CombinedData) -> VarData:
    dependent_variables = data.get_vars(dv_identifier)
    assert len(dependent_variables) <= 1, \
        "Only one dependent variable expected instead of %d" % len(dependent_variables)
    return dependent_variables[0] if len(dependent_variables) else None


def independent_variable_is_categorical(data: CombinedData) -> bool:
    independent_variable = get_independent_variable(data)
    return independent_variable and independent_variable.is_categorical()


def independent_variable_is_continuous(data: CombinedData) -> bool:
    independent_variable = get_independent_variable(data)
    return independent_variable and independent_variable.is_continuous()


def independent_variable_has_enough_categories(data: CombinedData, num_categories=2) -> bool:
    return independent_variable_is_categorical(data) and \
        get_independent_variable(data).get_number_categories() >= num_categories


def dependent_variable_is_categorical(data: CombinedData) -> bool:
    dependent_variable = get_dependent_variable(data)
    return dependent_variable and dependent_variable.is_categorical()


def dependent_variable_is_continuous(data: CombinedData) -> bool:
    dependent_variable = get_dependent_variable(data)
    return dependent_variable and dependent_variable.is_continuous()


def dependent_variable_is_ordinal(data: CombinedData) -> bool:
    dependent_variable = get_dependent_variable(data)
    return dependent_variable and dependent_variable.is_ordinal()


def find_applicable_bivariate_tests(data: CombinedData):
    def bool_val(cond):
        return BoolVal(True) if cond else BoolVal(False)

    students_t = Bool('students_t')
    u_test = Bool('u_test')
    # chi_square = Bool('chi_square')
    # pearson_correlation = Bool('pearson_correlation')
    # paired_t = Bool('paired_t')
    # spearman_correlation = Bool('spearman_correlation')
    # wilcoxon_sign_rank = Bool('wilcoxon_sign_rank')
    # binomial_test = Bool('binomial_test')

    max_sat = Optimize()
    max_sat.add(students_t == And(bool_val(independent_variable_is_categorical(data)),
                                  bool_val(independent_variable_has_enough_categories(data, num_categories=2)),
                                  bool_val(not data.has_paired_observations()),
                                  bool_val(dependent_variable_is_continuous(data)),
                                  bool_val(data.has_equal_variance())))

    max_sat.add(u_test == And(bool_val(data.has_equal_variance()),
                              bool_val(not data.has_paired_observations()),
                              bool_val(independent_variable_is_categorical(data)),
                              bool_val(dependent_variable_is_continuous(data)
                                       or dependent_variable_is_ordinal(data))))

    # max_sat.add(chi_square == And(bool_val(test_information.all_variables_have_independent_observations),
    #                               bool_val(test_information.all_variables_are_categorical),
    #                               bool_val(test_information.all_variables_have_enough_samples),
    #                               bool_val(test_information.all_variables_have_enough_categories)))
    #
    #
    # max_sat.add(pearson_correlation == And(bool_val(test_information.all_variables_have_independent_observations),
    #                                        bool_val(test_information.all_variables_are_continuous),
    #                                        bool_val(test_information.is_bivariate_normal)))
    #
    # max_sat.add(paired_t == And(bool_val(test_information.all_variables_are_continuous),
    #                             bool_val(test_information.observations_are_paired),
    #                             bool_val(test_information.difference_between_paired_values_is_normal)))
    #
    # max_sat.add(spearman_correlation == And(bool_val(test_information.all_variables_are_continuous_or_ordinal)))
    #
    # # Not sure how to test that the difference between related groups is symmetrical in shape, so for
    # # now leave that as an assumption.
    # max_sat.add(wilcoxon_sign_rank == And(bool_val(test_information.dependent_variable_is_continuous
    #                                                or test_information.dependent_variable_is_ordinal),
    #                                       bool_val(test_information.independent_variable_is_categorical),
    #                                       bool_val(test_information.observations_are_paired)))
    #
    # max_sat.add(binomial_test == And(bool_val(test_information.dependent_variable_is_categorical),
    #                                  bool_val(test_information.dependent_variable_has_num_categories(2))))

    max_sat.add_soft(students_t)
    max_sat.add_soft(u_test)
    # max_sat.add_soft(chi_square)
    # max_sat.add_soft(pearson_correlation)
    # max_sat.add_soft(paired_t)
    # max_sat.add_soft(spearman_correlation)
    # max_sat.add_soft(wilcoxon_sign_rank)
    # max_sat.add_soft(binomial_test)

    tests_and_assumptions = {}
    if max_sat.check() == sat:
        model = max_sat.model()
        if model[students_t]:
            tests_and_assumptions[Tests.STUDENTST] = assumptions_for_test(Tests.STUDENTST)
        if model[chi_square]:
            tests_and_assumptions[Tests.CHISQUARE] = assumptions_for_test(Tests.CHISQUARE)
        if model[u_test]:
            tests_and_assumptions[Tests.UTEST] = assumptions_for_test(Tests.UTEST)
        if model[pearson_correlation]:
            tests_and_assumptions[Tests.PEARSON_CORRELATION] = assumptions_for_test(Tests.PEARSON_CORRELATION)
        if model[paired_t]:
            tests_and_assumptions[Tests.PAIRED_SAMPLES_TTEST] = assumptions_for_test(Tests.PAIRED_SAMPLES_TTEST)
        if model[spearman_correlation]:
            tests_and_assumptions[Tests.SPEARMAN_CORRELATION] = assumptions_for_test(Tests.SPEARMAN_CORRELATION)
        if model[wilcoxon_sign_rank]:
            tests_and_assumptions[Tests.WILCOXON_SIGN_RANK_TEST] = assumptions_for_test(Tests.WILCOXON_SIGN_RANK_TEST)
        if model[binomial_test]:
            tests_and_assumptions[Tests.BINOMIAL_TEST] == assumptions_for_test(Tests.BINOMIAL_TEST)

    return tests_and_assumptions


def find_applicable_bivariate_tests_with_temp_data_structure(test_information: BivariateTestInformation):
    def bool_val(cond):
        return BoolVal(True) if cond else BoolVal(False)

    students_t = Bool('students_t')
    chi_square = Bool('chi_square')
    u_test = Bool('u_test')
    pearson_correlation = Bool('pearson_correlation')
    paired_t = Bool('paired_t')
    spearman_correlation = Bool('spearman_correlation')
    wilcoxon_sign_rank = Bool('wilcoxon_sign_rank')
    binomial_test = Bool('binomial_test')

    max_sat = Optimize()
    max_sat.add(students_t == And(bool_val(test_information.all_variables_have_independent_observations),
                                  bool_val(test_information.independent_variable_is_categorical),
                                  bool_val(test_information.independent_variable_has_enough_categories),
                                  bool_val(not test_information.observations_are_paired),
                                  bool_val(test_information.dependent_variable_is_continuous),
                                  bool_val(test_information.samples_have_similar_variances)))

    max_sat.add(chi_square == And(bool_val(test_information.all_variables_have_independent_observations),
                                  bool_val(test_information.all_variables_are_categorical),
                                  bool_val(test_information.all_variables_have_enough_samples),
                                  bool_val(test_information.all_variables_have_enough_categories)))

    max_sat.add(u_test == And(bool_val(test_information.all_variables_have_independent_observations),
                              bool_val(test_information.samples_have_similar_variances),
                              bool_val(not test_information.observations_are_paired),
                              bool_val(test_information.independent_variable_is_categorical),
                              bool_val(test_information.dependent_variable_is_continuous
                                       or test_information.dependent_variable_is_ordinal)))

    max_sat.add(pearson_correlation == And(bool_val(test_information.all_variables_have_independent_observations),
                                           bool_val(test_information.all_variables_are_continuous),
                                           bool_val(test_information.is_bivariate_normal)))

    max_sat.add(paired_t == And(bool_val(test_information.all_variables_are_continuous),
                                bool_val(test_information.observations_are_paired),
                                bool_val(test_information.difference_between_paired_values_is_normal)))

    max_sat.add(spearman_correlation == And(bool_val(test_information.all_variables_are_continuous_or_ordinal)))

    # Not sure how to test that the difference between related groups is symmetrical in shape, so for
    # now leave that as an assumption.
    max_sat.add(wilcoxon_sign_rank == And(bool_val(test_information.dependent_variable_is_continuous
                                                   or test_information.dependent_variable_is_ordinal),
                                          bool_val(test_information.independent_variable_is_categorical),
                                          bool_val(test_information.observations_are_paired)))

    max_sat.add(binomial_test == And(bool_val(test_information.dependent_variable_is_categorical),
                                     bool_val(test_information.dependent_variable_has_num_categories(2))))

    max_sat.add_soft(students_t)
    max_sat.add_soft(chi_square)
    max_sat.add_soft(u_test)
    max_sat.add_soft(pearson_correlation)
    max_sat.add_soft(paired_t)
    max_sat.add_soft(spearman_correlation)
    max_sat.add_soft(wilcoxon_sign_rank)
    max_sat.add_soft(binomial_test)

    tests_and_assumptions = {}
    if max_sat.check() == sat:
        model = max_sat.model()
        if model[students_t]:
            tests_and_assumptions[Tests.STUDENTST] = assumptions_for_test(Tests.STUDENTST)
        if model[chi_square]:
            tests_and_assumptions[Tests.CHISQUARE] = assumptions_for_test(Tests.CHISQUARE)
        if model[u_test]:
            tests_and_assumptions[Tests.UTEST] = assumptions_for_test(Tests.UTEST)
        if model[pearson_correlation]:
            tests_and_assumptions[Tests.PEARSON_CORRELATION] = assumptions_for_test(Tests.PEARSON_CORRELATION)
        if model[paired_t]:
            tests_and_assumptions[Tests.PAIRED_SAMPLES_TTEST] = assumptions_for_test(Tests.PAIRED_SAMPLES_TTEST)
        if model[spearman_correlation]:
            tests_and_assumptions[Tests.SPEARMAN_CORRELATION] = assumptions_for_test(Tests.SPEARMAN_CORRELATION)
        if model[wilcoxon_sign_rank]:
            tests_and_assumptions[Tests.WILCOXON_SIGN_RANK_TEST] = assumptions_for_test(Tests.WILCOXON_SIGN_RANK_TEST)
        if model[binomial_test]:
            tests_and_assumptions[Tests.BINOMIAL_TEST] == assumptions_for_test(Tests.BINOMIAL_TEST)

    return tests_and_assumptions


# Test by creating some sample data.
dependent_variable1 = VariableInformation(has_independent_samples=True, is_normal=True, variance=0.06, sample_size=35,
                                          is_continuous=True, is_dependent_variable=True)
dependent_variable2 = VariableInformation(has_independent_samples=True, is_normal=True, variance=0.06, sample_size=55,
                                          is_continuous=True, is_dependent_variable=True)
independent_variable = VariableInformation(has_independent_samples=True, is_categorical=True,
                                           number_of_categories=2, is_independent_variable=True)

# ttest_information = BivariateTestInformation(variables=[dependent_variable1, dependent_variable2, independent_variable],
#                                              similar_variances=True)

categorical_variable1 = VariableInformation(has_independent_samples=True, is_normal=False,
                                            is_categorical=True, sample_size=35, number_of_categories=2)
categorical_variable2 = VariableInformation(has_independent_samples=True, is_normal=False, is_categorical=True,
                                            sample_size=30, number_of_categories=5)

# categorical_test_information = BivariateTestInformation(variables=[categorical_variable1, categorical_variable2])

print("Tests for normal samples:")
# for test, assumptions in find_applicable_bivariate_tests(ttest_information).items():
#     print("%s: %s" % (test, assumptions))

print("\nTests for categorical samples:")
# for test, assumptions in find_applicable_bivariate_tests(categorical_test_information).items():
#     print("%s: %s" % (test, assumptions))
