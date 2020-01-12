## Abstract Factory pattern to create Hypotheses

import attr

from tea.global_vals import *
from tea.runtimeDataStructures.design import AbstractDesign, ObservationalDesign, ExperimentDesign
from tea.runtimeDataStructures.variable import AbstractVariable

class AbstractHypothesis(object): 

    original_hypothesis: str # original string hypothesis that the end-user writes

    def __init__(self, hypothesis: str):
        self.original_hypothesis = hypothesis # store the original string the end user wrote
    
    @classmethod
    def create(cls, hypothesis: str, variables: list, design: AbstractDesign): 
        # First, make sure that hypothesis fits one of the supported templates
        for hypo_syn in HYPOTHESIS_SYNTAX: 
            if hypo_syn in hypothesis: 
                # Second, determine which template was used, create appropriate Hypothesis object for provided hypothesis
                # Hypothesis involves categorical groups?
                if hypo_syn in GROUP_COMPARISONS: 
                    return GroupComparisons.create(hypothesis, variables, design) # TODO: May just want one GroupComparisons (not Bivariate vs. Multivariate) class/object
                # Hypothesis involves linear relationships?
                elif hypo_syn in LINEAR_RELATIONSHIP: 
                    return LinearHypothesis(hypothesis, variables, design)
                else: 
                    raise ValueError(f"Unknown hypothesis form: {hypothesis}")
        raise ValueError(f"Unknown hypothesis form: {hypothesis}")

    # @param delimiter is a list of keywords that are acceptable to specify/distinguish which hypothesis template is used
    # @returns a Dict of rhs and lhs 
    def parse_hypothesis(self, possible_delims: list): 
        # assert that the delimiter exists in the hypothesis
        dlms_in_hypothesis = [dlm for dlm in possible_delims if dlm in self.original_hypothesis]
        assert(len(dlms_in_hypothesis) == 1) #currently only allow for one delimiter to be present in hypothesis

        # Get the delimiter (of the @param possible_delims)
        delim = None
        for dlm in possible_delims: 
            if dlm in self.original_hypothesis:
                if delim is None:
                    delim = dlm
                else: 
                    raise ValueError(f"Invalid hypothesis. Hypothesis ({self.original_hypothesis}) has more than one delimiter. Should only have one of {possible_delims}.")
        
        # extract rhs and lhs
        delimiter_ind = self.original_hypothesis.index(delim)
        rhs = self.original_hypothesis[:delimiter_ind].strip()
        lhs = self.original_hypothesis[delimiter_ind+len(delim):].strip()

        # TODO: What format are the rhs and lhs? Even before return as lists?
        return ([rhs], [lhs])

@attr.s(init=False)
class LinearHypothesis(AbstractHypothesis): 
    xs : list # list of x variables (of type AbstractVariable)
    y: list # list of y variable, assert that the length is one/only one y variable (of type AbstractVariable)

    # @param hypothesis: str representing end-user's hypothesis 
    # @param variables: list of Variables 
    # @param design: one of the subclasses of AbstractDesign, could be ObservationalDesign or ExperimentDesign
    def __init__(self, hypothesis: str, variables: list, design: AbstractDesign):
        super().__init__(hypothesis) # store the original string the end user wrote
        self.xs = []
        self.y = []
        
        rhs_names, lhs_names = self.parse_hypothesis(LINEAR_RELATIONSHIP)

        # Then expand to the case where have + and - 
        
        rhs_vars = [AbstractVariable.get_variable(variables, name) for name in rhs_names] # get rhs Variables
        lhs_vars = [AbstractVariable.get_variable(variables, name) for name in lhs_names] # get lhs Variables
        all_vars = rhs_vars + lhs_vars # all vars 

        # Based on Design, figure out which role the Variables in the Hypothesis play
        for var in all_vars: 
            assert(isinstance(var, AbstractVariable))
            role = design.which_role(var)
            # Assign Variables to appropriate Hypothesis fields
            if role == 'X':
                self.xs.append(var)
            else: 
                assert(role == 'Y')
                self.y.append(var)
        import pdb; pdb.set_trace()

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