from enum import Flag, auto
from z3-solver import *

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


def independent_variable_has_number_of_categories(data: CombinedData, num_categories=2) -> bool:
    return independent_variable_is_categorical(data) and \
        get_independent_variable(data).get_number_categories() == num_categories


def dependent_variable_is_categorical(data: CombinedData) -> bool:
    dependent_variable = get_dependent_variable(data)
    return dependent_variable and dependent_variable.is_categorical()


def dependent_variable_has_number_of_categories(data: CombinedData, num_categories=2) -> bool:
    return dependent_variable_is_categorical(data) and \
        get_dependent_variable(data).get_number_categories() == num_categories


def dependent_variable_is_continuous(data: CombinedData) -> bool:
    dependent_variable = get_dependent_variable(data)
    return dependent_variable and dependent_variable.is_continuous()


def dependent_variable_is_ordinal(data: CombinedData) -> bool:
    dependent_variable = get_dependent_variable(data)
    return dependent_variable and dependent_variable.is_ordinal()


def dependent_variable_is_normal(data: CombinedData) -> bool:
    dependent_variable = get_dependent_variable(data)
    return dependent_variable and dependent_variable.is_continuous() and dependent_variable.is_normal(0.05)


def all_elements_satisfy_property(elements, check_property):
    return not next((element for element in elements if not check_property(element)), None)


def all_variables_are_categorical(data: CombinedData) -> bool:
    return all_elements_satisfy_property(data.vars, lambda var: var.is_categorical())


def all_variables_are_continuous(data: CombinedData) -> bool:
    return all_elements_satisfy_property(data.vars, lambda var: var.is_continuous())


def all_variables_are_normal(data: CombinedData) -> bool:
    return all_elements_satisfy_property(data.vars, lambda var: var.is_continuous() and var.is_normal(0.05))


def all_variables_are_continuous_or_ordinal(data: CombinedData) -> bool:
    return all_elements_satisfy_property(data.vars, lambda var: var.is_continuous() or var.is_ordinal())


def all_variables_have_enough_categories(data: CombinedData, number_of_categories=2) -> bool:
    return all_variables_are_categorical(data) and \
           all_elements_satisfy_property(data.vars, lambda var: var.get_number_categories() >= number_of_categories)


def all_variables_have_enough_samples(data: CombinedData, num_samples=30) -> bool:
    return all_elements_satisfy_property(data.vars, lambda var: var.get_sample_size() >= num_samples)


def all_variables_have_same_number_of_samples(data: CombinedData) -> bool:
    number_of_samples = data.vars[0].get_sample_size()
    return all_elements_satisfy_property(data.vars, lambda var: var.get_sample_size() == number_of_samples)


def find_applicable_bivariate_tests(data: CombinedData):
    def bool_val(cond):
        return BoolVal(True) if cond else BoolVal(False)

    students_t = Bool('students_t')
    u_test = Bool('u_test')
    chi_square = Bool('chi_square')
    pearson_correlation = Bool('pearson_correlation')
    paired_t = Bool('paired_t')
    spearman_correlation = Bool('spearman_correlation')
    wilcoxon_sign_rank = Bool('wilcoxon_sign_rank')
    binomial_test = Bool('binomial_test')

    max_sat = Optimize()
    max_sat.add(students_t == And(bool_val(independent_variable_is_categorical(data)),
                                  bool_val(independent_variable_has_number_of_categories(data, num_categories=2)),
                                  bool_val(not data.has_paired_observations()),
                                  bool_val(dependent_variable_is_continuous(data)),
                                  bool_val(dependent_variable_is_normal(data)),
                                  bool_val(data.has_equal_variance())))

    max_sat.add(u_test == And(bool_val(data.has_equal_variance()),
                              bool_val(not data.has_paired_observations()),
                              bool_val(independent_variable_is_categorical(data)),
                              bool_val(dependent_variable_is_continuous(data)
                                       or dependent_variable_is_ordinal(data))))

    max_sat.add(chi_square == And(bool_val(all_variables_are_categorical(data)),
                                  bool_val(all_variables_have_enough_samples(data)),
                                  bool_val(all_variables_have_enough_categories(data))))

    max_sat.add(pearson_correlation == And(bool_val(all_variables_are_continuous(data)),
                                           bool_val(all_variables_are_normal(data)),
                                           bool_val(all_variables_have_same_number_of_samples(data))))

    max_sat.add(paired_t == And(bool_val(independent_variable_is_categorical(data)),
                                bool_val(independent_variable_has_number_of_categories(data, 2)),
                                bool_val(dependent_variable_is_continuous(data)),
                                bool_val(data.has_paired_observations()),
                                bool_val(data.difference_between_paired_value_is_normal())))

    max_sat.add(spearman_correlation == And(bool_val(all_variables_are_continuous_or_ordinal(data)),
                                            bool_val(all_variables_have_same_number_of_samples(data))))

    # Not sure how to test that the difference between related groups is symmetrical in shape, so for
    # now leave that as an assumption.
    max_sat.add(wilcoxon_sign_rank == And(bool_val(dependent_variable_is_continuous(data)
                                                   or dependent_variable_is_ordinal(data)),
                                          bool_val(independent_variable_is_categorical(data)),
                                          bool_val(independent_variable_has_number_of_categories(data, 2)),
                                          bool_val(data.has_paired_observations())))

    max_sat.add(binomial_test == And(bool_val(dependent_variable_is_categorical(data)),
                                     bool_val(dependent_variable_has_number_of_categories(data, 2))))

    max_sat.add_soft(students_t)
    max_sat.add_soft(u_test)
    max_sat.add_soft(chi_square)
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
