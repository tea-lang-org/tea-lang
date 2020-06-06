from tea.global_vals import *
from tea.helpers.constants.test_names import *
from enum import Enum
from .value import Value
from tea.ast import DataType, LessThan, GreaterThan, Literal, Relationship

# Other
import attr


# Need to be reset for each test
group1 = None
group2 = None
outcome = None

__test_to_statistic_of_interest__ = {
    STUDENTS_T_NAME: "mean",
    WELCHS_T_NAME: "mean",
    MANN_WHITNEY_NAME: "median",
    PAIRED_STUDENTS_NAME: "mean",
    WILCOXON_SIGNED_RANK_NAME: "median",
    KRUSKALL_WALLIS_NAME: "median",
    FACTORIAL_ANOVA_NAME: "mean",
}

__stats_tests_to_null_hypotheses__ = {
    PEARSON_NAME:  'There is no relationship between {} and {}.',
    KENDALLTAU_NAME: 'There is no relationship between {} and {}.',
    SPEARMAN_NAME: 'There is no monotonic relationship between {} and {}.',
    POINTBISERIAL_NAME: 'There is no association between {} and {}.',

    STUDENTS_T_NAME : 'There is no difference in {}s between {} and {} on {}.',
    WELCHS_T_NAME : 'There is no difference in {}s between {} and {} on {}.',
    MANN_WHITNEY_NAME : 'There is no difference in {}s between {} and {} on {}.',
    PAIRED_STUDENTS_NAME : 'There is no difference in {}s between {} and {} on {}.',
    WILCOXON_SIGNED_RANK_NAME : 'There is no difference in {}s between {} and {} on {}.',

    CHI_SQUARE_NAME : 'There is no association between {} and {} on {}.',
    FISHER_EXACT_NAME : 'There is no association between {} and {} on {}.',

    # Regression or anova?
    F_TEST_NAME : 'The variances of the groups ({}) are{}equal.',
    KRUSKALL_WALLIS_NAME : 'There is no difference in {}s between {} on {}.',
    # This isn't very descriptive…
    "Friedman" : f'There is no difference between the groups',
    FACTORIAL_ANOVA_NAME : 'There is no difference in {}s between {} on {}.',
    RM_ONE_WAY_ANOVA_NAME : 'The means of all groups/conditions ({}) are{}equal.',

    # Does this depend on the statistic being calculated?
    "Bootstrap" : f''
}

__two_group_tests__ = {
    PEARSON_NAME,
    KENDALLTAU_NAME,
    SPEARMAN_NAME,
    POINTBISERIAL_NAME,
}

__two_group_outcome_tests__ = {
    STUDENTS_T_NAME,
    WELCHS_T_NAME,
    MANN_WHITNEY_NAME,
    PAIRED_STUDENTS_NAME,
    WILCOXON_SIGNED_RANK_NAME,
}

__categorical_tests__ = {
    CHI_SQUARE_NAME,
    FISHER_EXACT_NAME,
}

__many_groups_test__ = {
    RM_ONE_WAY_ANOVA_NAME,
    F_TEST_NAME,
}

__many_groups_outcome_tests__ = {
    KRUSKALL_WALLIS_NAME,
    FACTORIAL_ANOVA_NAME,
}


@attr.s(init=True)
class TestResult(Value): 
    name = attr.ib()
    test_statistic = attr.ib()
    p_value = attr.ib()
    prediction = attr.ib()
    alpha = attr.ib()
    dof = attr.ib(default=None)
    adjusted_p_value = attr.ib(default=None)
    corrected_p_value = attr.ib(default=None) # for multiple comparisons
    null_hypothesis = attr.ib(default=None)
    interpretation = attr.ib(default=None)
    table = attr.ib(default=None)
    x = attr.ib(default=None)
    y = attr.ib(default=None)
    group_descriptive_statistics = attr.ib(default=None)

    def __attrs_post_init__(self):
        self.adjust_p_val()

        # TODO: Handle more cases without a prediction.
        if self.prediction or (self.x and self.y):
            self.null_hypothesis = self.get_null_hypothesis()
            self.set_interpretation()
        else:
            print("No prediction specified.")

    def adjust_p_val(self): 
        # Adjust p value if it has not already been adjusted
        if not self.adjusted_p_value:
            if self.prediction or (self.x and self.y):
                if self._is_one_sided():
                    self.adjusted_p_value = self.p_value/2
                else: 
                    self.adjusted_p_value = self.p_value

    def bonferroni_correction(self, num_comparisons):
        assert(num_comparisons >= 1)
        
        # Does it already have an adjusted p value?
        if self.adjusted_p_value:
            self.corrected_p_value = self.adjusted_p_value/(num_comparisons * 1.0)

        else: 
            if isinstance(self.p_value, float): # Self is not a result from Bootstrapping
                self.corrected_p_value = self.p_value/(num_comparisons * 1.0)

        ## FOR DEBUGGING
        # if num_comparisons != 1:
        #     import pdb; pdb.set_trace()

    def get_null_hypothesis(self):
        # TODO: Passing x and y seems more modular than passing string?
        if self.name in __two_group_tests__:
            var1, var2 = self._calculate_two_group_vars()
            return __stats_tests_to_null_hypotheses__[self.name] \
                .format(var1, var2)
        elif self.name in __two_group_outcome_tests__:
            assert self.x
            assert len(self.x.metadata[categories]) == 2
            assert self.y

            cats = list(self.x.metadata[categories].items())
            return __stats_tests_to_null_hypotheses__[self.name] \
                .format(__test_to_statistic_of_interest__[self.name], f"{self.x.metadata[name]} = {cats[0][0]}", f"{self.x.metadata[name]} = {cats[1][0]}", self.y.metadata[name])
        elif self.name in __many_groups_test__:
            assert self.x
            assert len(self.x.metadata[categories]) > 0

            return __stats_tests_to_null_hypotheses__[self.name] \
                .format(self._get_all_groups(), " ")
        elif self.name in __many_groups_outcome_tests__:
            assert self.x
            assert self.y

            return __stats_tests_to_null_hypotheses__[self.name] \
                .format(__test_to_statistic_of_interest__[self.name], self._get_all_groups(), self.y.metadata[name])
        elif self.name in __categorical_tests__:
            assert self.x
            assert self.y
            var1, var2 = self._calculate_two_group_vars()
            return __stats_tests_to_null_hypotheses__[self.name] \
                .format(var1, var2, self.y.metadata[name])
        return ""

    def set_interpretation(self):
        """
            Based on https://stats.idre.ucla.edu/other/mult-pkg/faq/general/faq-what-are-the-differences-between-one-tailed-and-two-tailed-tests/
            From the example on this site:
            If t is negative and we are checking a less than relationship, use p/2 as the adjusted p-value.
            If t is negative and we are checking a greater than relationship, use 1 - p/2 as the adjusted p-value.
        """

        # import pdb; pdb.set_trace()
        # one_sided = True if self.adjusted_p_value else False
        one_sided = self._is_one_sided()

        # Start interpretation
        ttest_result = Significance.not_significant
        if self.test_statistic > 0:
            if one_sided and isinstance(self.prediction, GreaterThan) and self.adjusted_p_value < self.alpha:
                ttest_result = Significance.significantly_greater
            elif one_sided and isinstance(self.prediction, LessThan) and 1 - self.adjusted_p_value < self.alpha:
                ttest_result = Significance.significantly_less
            elif not one_sided and self.adjusted_p_value and self.adjusted_p_value < self.alpha:
                ttest_result = Significance.significantly_different
            else:
                ttest_result = Significance.not_significant
        elif self.test_statistic < 0:
            if one_sided and isinstance(self.prediction, LessThan) and  1 - self.adjusted_p_value < self.alpha:
                ttest_result = Significance.significantly_less
            elif one_sided and isinstance(self.prediction, GreaterThan) and self.adjusted_p_value < self.alpha:
                ttest_result = Significance.significantly_greater
            elif not one_sided and self.adjusted_p_value < self.alpha:
                ttest_result = Significance.significantly_different
            else:
                ttest_result = Significance.not_significant
        elif not one_sided and self.adjusted_p_value and self.adjusted_p_value < self.alpha:
            ttest_result = ttest_result.significantly_different
        else:
            assert False, "test_statistic = 0 and it's not a one-sided test. Not sure under what conditions this is possible."


        # TODO Maybe the "means" part could be replacable....
        self.interpretation = f"t({self.dof}) = {'%.5f'%(self.test_statistic)}, p = {'%.5f'%(self.adjusted_p_value)}. " if self.dof else ""
        if ttest_result == ttest_result.not_significant:
            self.interpretation += f"Fail to reject the null hypothesis at alpha = {self.alpha}. "
            self.interpretation += self.null_hypothesis
            # self.interpretation = f"The difference in means of {y.metadata[name]} for {x.metadata[name]} = {self.prediction.lhs.value} " \
            #     f"and {x.metadata[name]} = {self.prediction.rhs.value} is not significant."
        elif ttest_result == ttest_result.significantly_different:
            self.interpretation += f"Reject the null hypothesis at alpha = {self.alpha}. "
            if self.name in __two_group_tests__:
                var1, var2 = self._calculate_two_group_vars()
                self.interpretation += f"There is a relationship between {var1} and {var2}."
            elif self.name in __two_group_outcome_tests__:
                var1, var2 = self._calculate_two_group_outcome_vars()
                stat = __test_to_statistic_of_interest__[self.name]
                self.interpretation += f"The difference in {stat}s of {self.y.metadata[name]} for {self.x.metadata[name]} = {var1} " \
                    f"and {self.x.metadata[name]} = {var2} is significant. "
            elif self.name in __many_groups_test__:
                self.interpretation += __stats_tests_to_null_hypotheses__[self.name] \
                    .format(self._get_all_groups(), " not ")
            elif self.name in __many_groups_outcome_tests__:
                stat = __test_to_statistic_of_interest__[self.name]
                self.interpretation += f"There is a difference in {stat}s of {self.y.metadata[name]} for at least one of {self._get_all_groups()}."
            elif self.name in __categorical_tests__:
                var1, var2 = self._calculate_two_group_vars()
                self.interpretation += f"There is an association between {var1} and {var2} on {self.y.metadata[name]}."

        elif ttest_result == ttest_result.significantly_greater:
            self.interpretation += f"Reject the null hypothesis at alpha = {self.alpha}. "
            stat = __test_to_statistic_of_interest__[self.name]
            var1, var2 = self._calculate_two_group_outcome_vars()
            self.interpretation += f"The {stat} of {self.y.metadata[name]} for {self.x.metadata[name]} = {var1} is significantly" \
                f" greater than the {stat} for {self.x.metadata[name]} = {var2}. "
        elif ttest_result == ttest_result.significantly_less:
            self.interpretation += f"Reject the null hypothesis at alpha = {self.alpha}. "
            stat = __test_to_statistic_of_interest__[self.name]
            var1, var2 = self._calculate_two_group_outcome_vars()
            self.interpretation += f"The {stat} of {self.y.metadata[name]} for {self.x.metadata[name]} = {var1} is significantly" \
                f" less than the {stat} for {self.x.metadata[name]} = {var2}. "
        else:
            assert False, "ttest_result case without an associated self.interpretation."

    # def adjust_p_val(self, correction): 
    #     self.self.adjusted_p_value = attr.ib()
    #     self.self.adjusted_p_value = self.p_value/correction
    
    # def set_adjusted_p_val(self, adjusted_p_value): 
    #     self.self.adjusted_p_value = attr.ib()
    #     self.self.adjusted_p_value = adjusted_p_value

    def add_effect_size(self, name, effect_size): 
        if hasattr(self, 'effect_size'):
            self.effect_size[name] = effect_size
        else: 
            self.effect_size = attr.ib()
            self.effect_size = {name: effect_size}

    def add_effect_size_to_interpretation(self):
        effect_sizes = ""
        for effect_size_name, effect_size_value in self.effect_size.items():
            effect_sizes += f"{effect_size_name} = {'%.5f' % effect_size_value}, "
        effect_sizes = effect_sizes[:-2]
        self.interpretation += f"The effect size is {effect_sizes}. " \
            f"The effect size is the magnitude of the difference, which gives a holistic view of the results [1].\n" \
            f"[1] Sullivan, G. M., & Feinn, R. (2012). Using effect size—or why the P value is not enough. Journal of graduate medical education, 4(3), 279-282."

    
    def add_doc(self, name, dof):
        import pdb; pdb.set_trace()

    def _calculate_two_group_vars(self):
        var1 = ""
        var2 = ""
        if self.prediction:
            if isinstance(self.prediction.lhs, Literal):
                var1 = self.prediction.lhs.value
                var2 = self.prediction.rhs.value
            else:
                assert isinstance(self.prediction.lhs, Relationship)
                # assert isinstance(self.prediction.lhs, Relationship)
                var1 = self.prediction.lhs.var
                var2 = self.prediction.rhs.var
        else:
            assert len(self.x.metadata[categories]) == 2
            cats = list(self.x.metadata[categories].items())
            var1 = cats[0][0]
            var2 = cats[1][0]

        return (var1, var2)

    def _calculate_two_group_outcome_vars(self):
        var1 = self.prediction.lhs.value
        var2 = self.prediction.rhs.value
        if self.group_descriptive_statistics:
            var1 = f"{var1} (M={'%.5f'%(self.group_descriptive_statistics[var1]['mean'])}, SD={'%.5f'%(self.group_descriptive_statistics[var1]['stdev'])})"
            var2 = f"{var2} (M={'%.5f'%(self.group_descriptive_statistics[var2]['mean'])}, SD={'%.5f'%(self.group_descriptive_statistics[var2]['stdev'])})"

        return (var1, var2)

    def _get_all_groups(self):
        assert self.x
        return self.x.metadata[name] + " = " + ', '.join([str(cat[0]) for cat in list(self.x.metadata[categories].items())])

    def _is_one_sided(self):
        return True if self.name in __two_group_outcome_tests__ and \
                        (isinstance(self.prediction, GreaterThan) or isinstance(self.prediction, LessThan)) \
                else False


class Significance(Enum): 
        not_significant = 0
        significantly_different = 1
        significantly_greater = 2
        significantly_less = 3