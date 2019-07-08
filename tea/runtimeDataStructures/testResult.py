from tea.global_vals import *
from enum import Enum
from .value import Value
from tea.ast import DataType, LessThan, GreaterThan

# Other
import attr


# Need to be reset for each test
group1 = None
group2 = None
outcome = None
__stats_tests_to_null_hypotheses__ = {

    "Pearson Correlation" : f'',
    "Kendall Tau Correlation" : f'',
    "Spearman Correlation" : f'',
    "Pointbiserial Correlation" : f'',

    "Student\'s T Test" : f'There is no difference in means between {group1} and {group2} on {outcome}.',
    "Welch\'s T Test" : f'There is no difference in means between {group1} and {group2} on {outcome}.',
    "Mann Whitney U Test" : 'range', # TODO
    "Paired Student\'s T Test" : f'There is no difference in means between {group1} and {group2} on {outcome}.',
    "Wilcoxon Signed Rank" : 'range', # TODO

    "Chi Square Test" : f'',
    "Fisher\'s Exact Test" : f'',

    "F Test" : f'',
    "Kruskall Wallis" : f'',
    "Friedman" : f'',
    "Factorial ANOVA" : f'',
    "Repeated Measures One Way ANOVA" : f'',

    "Bootstrap" : f''

}


@attr.s(init=True)
class TestResult(Value): 
    name = attr.ib()
    test_statistic = attr.ib()
    p_value = attr.ib()
    prediction = attr.ib()
    dof = attr.ib(default=None)
    adjusted_p_value = attr.ib(default=None)
    null_hypothesis = attr.ib(default=None)
    interpretation = attr.ib(default=None)

    def adjust_p_val(self):
        # Adjust p value
        if self.prediction: 

            one_sided = True if isinstance(self.prediction, GreaterThan) or isinstance(self.prediction, LessThan) else False

            if one_sided:
                self.adjusted_p_value = self.p_value/2
            else: 
                self.adjusted_p_value = self.p_value

    def specify_null_hypothesis(self, x, y):
        # TODO: Passing x and y seems more modular than passing string? 
        group1 = x #???
        group2 = x #??
        outcome = y #??

        self.null_hypothesis = __stats_tests_to_null_hypotheses__[self.name]

    def set_interpretation(self, alpha, x, y):
        """
            Based on https://stats.idre.ucla.edu/other/mult-pkg/faq/general/faq-what-are-the-differences-between-one-tailed-and-two-tailed-tests/
            From the example on this site:
            If t is negative and we are checking a less than relationship, use p/2 as the adjusted p-value.
            If t is negative and we are checking a greater than relationship, use 1 - p/2 as the adjusted p-value.
        """
        self.specify_null_hypothesis(x=x, y=y)

        # import pdb; pdb.set_trace()
        # one_sided = True if self.adjusted_p_value else False
        one_sided = True if isinstance(self.prediction, GreaterThan) or isinstance(self.prediction, LessThan) else False

        # Start interpretation
        ttest_result = Significance.not_significant
        if self.test_statistic > 0:
            if isinstance(self.prediction, GreaterThan) and self.adjusted_p_value < alpha:
                ttest_result = Significance.significantly_greater
            elif isinstance(self.prediction, LessThan) and 1 - self.adjusted_p_value < alpha:
                ttest_result = Significance.significantly_less
            elif not one_sided and self.adjusted_p_value and self.adjusted_p_value < alpha:
                ttest_result = Significance.significantly_different
            else:
                ttest_result = Significance.not_significant
        elif self.test_statistic < 0:
            if isinstance(self.prediction, LessThan) and self.adjusted_p_value < alpha:
                ttest_result = Significance.significantly_less
            elif isinstance(self.prediction, GreaterThan) and 1 - self.adjusted_p_value < alpha:
                ttest_result = Significance.significantly_greater
            elif not one_sided and self.adjusted_p_value < alpha:
                ttest_result = Significance.significantly_different
            else:
                ttest_result = Significance.not_significant
        elif not one_sided and self.adjusted_p_value and self.adjusted_p_value < alpha:
            ttest_result = ttest_result.significantly_different
        else:
            assert False, "test_statistic = 0 and it's not a one-sided test. Not sure under what conditions this is possible."


        # TODO Maybe the "means" part could be replacable....
        self.interpretation = None
        if ttest_result == ttest_result.not_significant:
            self.interpretation = f"The difference in means of {y.metadata[name]} for {x.metadata[name]} = {self.prediction.lhs.value} " \
                f"and {x.metadata[name]} = {self.prediction.rhs.value} is not significant."
        elif ttest_result == ttest_result.significantly_different:
            self.interpretation = f"The difference in means of {y.metadata[name]} for {x.metadata[name]} = {self.prediction.lhs.value} " \
                f"and {x.metadata[name]} = {self.prediction.rhs.value} is significant."
        elif ttest_result == ttest_result.significantly_greater:
            self.interpretation = f"The mean of {y.metadata[name]} for {x.metadata[name]} = {self.prediction.lhs.value} is significantly" \
                f" greater than the mean for {x.metadata[name]} = {self.prediction.rhs.value}"
        elif ttest_result == ttest_result.significantly_less:
            self.interpretation = f"The mean of {y.metadata[name]} for {x.metadata[name]} = {self.prediction.lhs.value} is significantly" \
                f" less than the mean for {x.metadata[name]} = {self.prediction.rhs.value}"
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
            self.effect_size = {name : effect_size}
    
    def add_doc(self, name, dof):
        import pdb; pdb.set_trace()

class Significance(Enum): 
        not_significant = 0
        significantly_different = 1
        significantly_greater = 2
        significantly_less = 3