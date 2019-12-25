## Abstract Factory pattern to create Hypotheses

import attr

from tea.global_vals import *
from tea.runtimeDataStructures.variable import AbstractVariable

class AbstractHypothesis(object): 
    
    @staticmethod
    def create(hypothesis: str): 
        # First, make sure that hypothesis fits one of the supported templates
        if HYPOTHESIS_SYNTAX in hypothesis: 
            # Second, determine which template was used, create appropriate Hypothesis object for provided hypothesis
            if GROUP_COMPARISONS in hypothesis: 
                return GroupComparisons.create(hypothesis) # TODO: May just want one GroupComparisons (not Bivariate vs. Multivariate) class/object
            elif LINEAR_RELATIONSHIP in hypothesis: 
                return LinearHypothesis(hypothesis)
            else: 
                raise ValueError(f"Unknown hypothesis form: {hypothesis}")
        else: 
            raise ValueError(f"Unknown hypothesis form: {hypothesis}")

@attr.s(init=False)
class LinearHypothesis(AbstractHypothesis): 
    original_hypothesis : str # original string hypothesis that the end-user writes
    xs : list # list of x variables (of type AbstractVariable)
    y: list # list of y variable, assert that the length is one/only one y variable (of type AbstractVariable)

    def __init__(self, hypo, variables):
        # TODO: get the variables
        pass

class GroupComparisons(AbstractHypothesis): 
    @staticmethod
    def create(hypothesis: str):
        assert(GROUP_COMPARISONS in hypothesis):

        
        # #TODO: If there are 2 groups
        # return BivariateComparisons(groups, hypothesis)

        # #TODO: If there are 3 groups
        # return MultipleComparisons(groups, hypothesis)

class BivariateComparisons(GroupComparisons):
    pass

class MultivariateComparisons(GroupComparisons):
    pass

# If there are multiple comparisons, maybe then there is some notion in the interpreter
# about calling all the subhypotheses, unifying them in a MultipleComparisons object and
# then performing correction ad hoc after (could be multiple correction methods)
class MultipleComparisons(object): 
    hypotheses : list # list of AbstractHypothesis objects

    pass