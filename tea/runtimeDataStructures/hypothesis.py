## Abstract Factory pattern to create Hypotheses

import attr

from tea.global_vals import *
from tea.runtimeDataStructures.design import AbstractDesign, ObservationalDesign, ExperimentDesign
from tea.runtimeDataStructures.variable import AbstractVariable, NominalVariable, OrdinalVariable, NumericVariable

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
                    return LinearHypothesis.create(hypothesis, variables, design)
                else: 
                    raise ValueError(f"Unknown hypothesis form: {hypothesis}")
        raise ValueError(f"Unknown hypothesis form: {hypothesis}")

    # @param delimiter is a list of keywords that are acceptable to specify/distinguish which hypothesis template is used
    @classmethod
    def parse_hypothesis(cls, hypothesis: str, possible_delims: list): 

        # assert that the delimiter exists in the hypothesis
        dlms_in_hypothesis = [dlm for dlm in possible_delims if dlm in hypothesis]
        assert(len(dlms_in_hypothesis) == 1) #currently only allow for one delimiter to be present in hypothesis

        # Get the delimiter (of the @param possible_delims)
        delim = None
        for dlm in possible_delims: 
            if dlm in hypothesis:
                if delim is None:
                    delim = dlm
                else: 
                    raise ValueError(f"Invalid hypothesis. Hypothesis ({hypothesis}) has more than one delimiter. Should only have one of {possible_delims}.")
        
        # extract rhs and lhs
        delimiter_ind = hypothesis.index(delim)
        rhs = hypothesis[:delimiter_ind].strip()
        lhs = hypothesis[delimiter_ind+len(delim):].strip()

        return (rhs, lhs)

@attr.s(init=False)
class LinearHypothesis(AbstractHypothesis): 

    def __init__(self, hypothesis: str):
        super().__init__(hypothesis) # store the original string the end user wrote

        
    @classmethod
    def create(cls, hypothesis: str, variables: list, design: AbstractDesign):
        rhs_name, lhs_name = super(LinearHypothesis, cls).parse_hypothesis(hypothesis, LINEAR_RELATIONSHIP)
        
        if lhs_name.startswith(NEGATIVE):  # "as LHS decreases,..."
            lhs_name = lhs_name[1:]
            lhs_dir = NEGATIVE
            lhs_var = AbstractVariable.get_variable(variables, lhs_name)
        elif lhs_name.startswith(POSITIVE):
            lhs_name = lhs_name = lhs_name[1:]
            lhs_dir = POSITIVE
            lhs_var = AbstractVariable.get_variable(variables, lhs_name)
        else: 
            lhs_dir = POSITIVE
            lhs_var = AbstractVariable.get_variable(variables, lhs_name)

        if rhs_name.startswith(NEGATIVE):
            rhs_name = rhs_name[1:]
            rhs_dir = NEGATIVE
            rhs_var = AbstractVariable.get_variable(variables, rhs_name)
        elif rhs_name.startswith(POSITIVE):
            rhs_name = rhs_name[1:]
            rhs_dir = POSITIVE
            rhs_var = AbstractVariable.get_variable(variables, rhs_name)
        else:
            rhs_dir = POSITIVE
            rhs_var = AbstractVariable.get_variable(variables, rhs_name)

        # Check that a LinearRelationship is possible/makes sense
        if (isinstance(lhs_var, OrdinalVariable) or isinstance(lhs_var, NumericVariable)): 
            if (isinstance(rhs_var, OrdinalVariable) or isinstance(rhs_var, NumericVariable)): 
                    if lhs_dir == rhs_dir:  # handles +lhs, +rhs and -lhs,
                        return PositiveLinear(hypothesis, design, lhs_var, rhs_var)
                    else:  # handles +lhs, -rhs and -lhs, +rhs
                        return NegativeLinear(hypothesis, design, lhs_var, rhs_var)
            else: 
                assert(isinstance(rhs_var, NominalVariable))
                raise ValueError(f"Linear relationship malformed. Both variables (LHS and RHS) must be Ordinal or Numeric. RHS is {type(rhs_var)}")
        else: 
            raise ValueError(f"Linear relationship malformed. Both variables (LHS and RHS) must be Ordinal or Numeric. LHS is {type(lhs_var)}")

        

class PositiveLinear(LinearHypothesis):

    xs: list # list of RHS variables (of type AbstractVariable)
    y: list # list of LHS variable, assert that the length is one/only one y variable (of type AbstractVariable)

    # @param hypothesis: str representing end-user's hypothesis 
    # @param design: one of the subclasses of AbstractDesign, could be ObservationalDesign or ExperimentDesign
    # @param lhs_var: Variable representing LHS of original hypothesis
    # @param rhs_var: Variable representing RHS of original hypothesis
    def __init__(self, hypothesis: str, design: AbstractDesign, lhs_var: str, rhs_var: str):
        super().__init__(hypothesis) # store the original string the end user wrote
        self.xs = []
        self.y = []

        # Based on Design, figure out which role the Variables in the Hypothesis play
        # FYI: Currently does not enforce Y or X on left or right side of delimiter
        all_vars = [lhs_var, rhs_var]
        for var in all_vars: 
            assert(isinstance(var, AbstractVariable))
            role = design.which_role(var)
            # Assign Variables to appropriate private instance fields
            if role == 'X':
                self.xs.append(var)
            else: 
                assert(role == 'Y')
                self.y.append(var)
    
class NegativeLinear(LinearHypothesis):
    
    # TODO: Rename to RHS and LHS?
    xs: list # list of x variables (of type AbstractVariable)
    y: list # list of y variable, assert that the length is one/only one y variable (of type AbstractVariable)

    # @param hypothesis: str representing end-user's hypothesis 
    # @param design: one of the subclasses of AbstractDesign, could be ObservationalDesign or ExperimentDesign
    # @param lhs_var: Variable representing LHS of original hypothesis
    # @param rhs_var: Variable representing RHS of original hypothesis
    def __init__(self, hypothesis: str, design: AbstractDesign, lhs_var: str, rhs_var: str):
        super().__init__(hypothesis) # store the original string the end user wrote
        self.xs = []
        self.y = []

        # Based on Design, figure out which role the Variables in the Hypothesis play
        # FYI: Currently does not enforce Y or X on left or right side of delimiter
        all_vars = [lhs_var, rhs_var]
        for var in all_vars: 
            assert(isinstance(var, AbstractVariable))
            role = design.which_role(var)
            # Assign Variables to appropriate private instance fields
            if role == 'X':
                self.xs.append(var)
            else: 
                assert(role == 'Y')
                self.y.append(var)

class GroupComparisons(AbstractHypothesis): 
    @classmethod
    def create(cls, hypothesis: str, variables: list, design: AbstractDesign):
        import pdb; pdb.set_trace()
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