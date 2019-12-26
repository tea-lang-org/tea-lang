## Abstract Factory pattern to create Hypotheses

import attr

from tea.global_vals import *
from tea.runtimeDataStructures.design import AbstractDesign, ObservationalDesign, ExperimentDesign
from tea.runtimeDataStructures.variable import AbstractVariable

class AbstractHypothesis(object): 

    original_hypothesis: str # original string hypothesis that the end-user writes
    
    @classmethod
    def create(cls, hypothesis: str, variables: list, design: AbstractDesign): 
        # First, make sure that hypothesis fits one of the supported templates
        if HYPOTHESIS_SYNTAX in hypothesis: 
            # Second, determine which template was used, create appropriate Hypothesis object for provided hypothesis
            if GROUP_COMPARISONS in hypothesis: 
                return GroupComparisons.create(hypothesis, variables, design) # TODO: May just want one GroupComparisons (not Bivariate vs. Multivariate) class/object
            elif LINEAR_RELATIONSHIP in hypothesis: 
                return LinearHypothesis(hypothesis, variables, design)
            else: 
                raise ValueError(f"Unknown hypothesis form: {hypothesis}")
        else: 
            raise ValueError(f"Unknown hypothesis form: {hypothesis}")

    # @param delimiter is the keyword to specify/distinguish which hypothesis template is used
    # @returns a Dict of rhs and lhs 
    def parse_hypothesis(self, delimiter: str): 
        # assert that the delimiter exists in the hypothesis
        assert(delimiter in self.original_hypothesis)

        # extract rhs and lhs 
        delimiter_ind = self.original_hypothesis.index(delimiter)
        rhs = self.original_hypothesis[:delimiter_ind].strip()
        lhs = self.original_hypothesis[delimiter_ind+len(delimiter):].strip()

        return (rhs, lhs)

@attr.s(init=False)
class LinearHypothesis(AbstractHypothesis): 
    # original_hypothesis : str 
    xs : list # list of x variables (of type AbstractVariable)
    y: list # list of y variable, assert that the length is one/only one y variable (of type AbstractVariable)

    # @param hypothesis is a string of type 
    def __init__(self, hypothesis, variables: list, design: AbstractDesign):
        
        super.__init__(hypothesis) # store the original string the end user wrote
        
        rhs_name, lhs_name = self.parse_hypothesis(LINEAR_RELATIONSHIP)
        
        # First, assume that only return one variable
        # handle case where there are multiple variables
        # Then expand to the case where have + and - 
        
        rhs_var = AbstractVariable.get_variable(variables, rhs_name)
        lhs_var = AbstractVariable.get_variable(variables, lhs_name)

        which_role(rhs_var)
        # START HERE: Which role does each variable have, to assign to Xs or Y 

        if isinstance(design, ObservationalDesign):
            pass
        elif isinstance(design, ExperimentDesign):
            pass
        else: 
            raise ValueError(f"Design is neither an ObservationalDesign nor an ExperimentDesign: {design}")

        # decide on Ys based on experimental design? 

class GroupComparisons(AbstractHypothesis): 
    @classmethod
    def create(cls, hypothesis: str, variables: list, design: AbstractDesign):
        assert(GROUP_COMPARISONS in hypothesis)
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