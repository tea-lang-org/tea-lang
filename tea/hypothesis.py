from tea.global_vals import *

class AbstractHypothesis(object): 
    
    @staticmethod
    def create(hypothesis: str): 
        pass

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