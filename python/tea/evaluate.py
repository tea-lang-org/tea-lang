from .ast import *
from .dataset import Dataset

from scipy import stats # Stats library used
import statsmodels.api as sm
import statsmodels.formula.api as smf
import numpy as np # Use some stats from numpy instead

# Eval : Dataset -> Model -> List[Hyps] -> ????
# Eval : Model -> List[Hyps] -> (Dataset -> Result)


# class Evaluator(object):
#     def __init__(self, dataset, experiment_setup):
#         self.dataset = dataset.data #access to pd.DataFrame directly
#         self.experiment_setup = experiment_setup
#         self.stats = {}
    
#     def eval(self, model: Model):
#         self.stats = {}

#         dv = model.dependent_var
#         iv = model.eq_independent_vars
        
#         if (isinstance(iv, Variable)): # only one independent variable --> BIVARIATE ANALYSIS
#             if (iv.dtype == DataType.ORDINAL or iv.dtype == DataType.NOMINAL): 
#                 if (iv.etype == Experiment_DataType.BETWEEN_SUBJECTS): 
#                     if (dv.dtype == DataType.INTERVAL and isnormal(dv.data)): 
#                         # oneway interval ANOVA
#                         pass
#                     elif (dv.dtype == DataType.INTERVAL or dv.dtype == DataType.ORDINAL):
#                         # kruskal wallis 
#                         pass
#                     elif (dv.dtype == DataType.NOMINAL): 
#                         # chi square
#                         pass
#                     else: 
#                         raise ValueError(f"Do not support this yet: IV{iv.dtype}, {iv.etype} and DV{dv.dtype}, {dv.etype}")
#                 elif (iv.etype == Experiment_DataType.WITHIN_SUBJECTS):
#                     if (dv.dtype == DataType.INTERVAL and isnormal(dv.data)): 
#                         # one way repeated measures ANOVA
#                         pass
#                     elif (dv.dtype == DataType.INTERVAL or dv.dtype == DataType.ORDINAL): 
#                         # Friedman test
#                         pass
#                     elif (dv.dtype == DataType.NOMINAL):
#                         if (len(dv.categories) == 2): 
#                             # repeated measures logistic regression
#                             pass
#                         else: 
#                             print('What do we do here?')
#             else: # (iv.dtype == DataType.INTERVAL or iv.dtype == DataType.RATIO): 
#                 if (dv.dtype == DataType.INTERVAL and isnormal(dv.data)): 
#                     # correlation or simple linear regression
#                     pass
#                 elif (dv.dtype == DataType.INTERVAL or dv.dtype == DataType.ORDINAL): 
#                     # non-parametric correlation
#                     pass
#                 elif (dv.dtype == DataType.NOMINAL): 
#                     # simple logistic regression 
#                     pass
#                 else: 
#                     raise ValueError(f"Do not support this yet: IV{iv.dtype}, {iv.etype} and DV{dv.dtype}, {dv.etype}")

#         else: #multivariate analysis
#             # TODO: RATIO data? ORDINAL Data? 
#             if (dv.dtype == DataType.INTERVAL and isnormal(dv.data)):
#                 # multiple regression
#                 regression(self.dataset, model, self.stats)
#                 # ANCOVA 
#                 pass
#             elif (dv.dtype == DataType.NOMINAL): 
#                 # multiple logistic regression or discriminant analysis
#                 pass
#             else: 
#                 raise ValueError(f"Do not support this yet: IV{iv.dtype}, {iv.etype} and DV{dv.dtype}, {dv.etype}")


# def evaluate(dataset: Dataset, experiment_setup: Experiment_SetUp, model: Model, hypothesis: Hypothesis):
#     e = Evaluator(dataset, experiment_setup)
#     e.eval(model)
#     return e.stats

def evaluate(dataset: Dataset, expr: Node):
    if isinstance(expr, Variable):
        return dataset[expr.name]

    # Should add to Dataset? -- doing so could compromise atomicity???
    elif isinstance(expr, Filter): # returns a Variable
        var = Filter.var
        cond = Filter.condition

        ds.
        
        new_name = var.name + '_' + str(lower_bound) + '_to_' + str(upper_bound)

        return Variable(new_name)

        name = attr.ib()
    dtype = attr.ib(type=DataType)
    categories = attr.ib()
    drange = attr.ib()
    
    # children from which self/this Variable is "derived"
    rhs = attr.ib(type=Node)
    lhs = attr.ib(type=Node)

# def regression(dataset, model: Model, stats): 
#     eq = str(model.dependent_var) + '~' + str(model.eq_independent_vars)
#     m = smf.ols(formula=eq, data=dataset) # use patsy for R-style equations
#     results = m.fit()
#     stats[eq] = results._results.__dict__

# def isnormal(data): 
#     return 
