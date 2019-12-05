from tea.global_vals import *

class AbstractHypothesis(object): 
    
    @staticmethod
    def create(hypothesis: str): 
        pass

        # TODO Need some way to parse a string the end-user writes. (maybe some unique keywords or something for the different kinds of hypotheses?)
        # TODO Then construct/return the appropriately typed Hypothesis object

class LinearHypothesis(AbstractHypothesis): 
    pass

class GroupComparisons(AbstractHypothesis): 
    pass

# If there are multiple comparisons, maybe then there is some notion in the interpreter
# about calling all the subhypotheses, unifying them in a MultipleComparisons object and
# then performing correction ad hoc after (could be multiple correction methods)
class MultipleComparisons(object): 
    hypotheses : list # list of AbstractHypothesis objects

    pass