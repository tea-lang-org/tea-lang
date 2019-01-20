from .ast import *
from .dataset import Dataset

import attr
from typing import Any

from scipy import stats # Stats library used
import statsmodels.api as sm
import statsmodels.formula.api as smf
import numpy as np # Use some stats from numpy instead
import pandas as pd

# Eval : Dataset, Program (list of functions/stats) --> table of computed stats

# x = 1 
# -----
# y = 2
# -----
# z = x + y
# -------
# z = z + z
# ----------

# def f():
#     tree 

# f -> AST 


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


class Value(object):
    pass

@attr.s(init=True, auto_attribs=True)
class VarData(Value):
    dataframe: Any
    metadata: Any

def evaluate(dataset: Dataset, expr: Node):
    if isinstance(expr, Variable):
        dataframe = dataset[expr.name]
        metadata = dataset.get_variable_data(expr.name) # (dtype, categories)
        return VarData(dataframe, metadata)

    elif isinstance(expr, Literal):
        data = pd.Series([expr.value] * len(dataset.data), index=dataset.data.index) # Series filled with literal value
        metadata = None # metadata=None means literal
        return VarData(data, metadata)

    elif isinstance(expr, Equal):
        rhs = evaluate(dataset, expr.rhs)
        lhs = evaluate(dataset, expr.lhs)
        assert isinstance(rhs, VarData)
        assert isinstance(lhs, VarData)
        
        dataframe = rhs.dataframe[rhs.dataframe == lhs.dataframe]
        metadata = rhs.metadata
        return VarData(dataframe, metadata)

    elif isinstance(expr, NotEqual): 
        rhs = evaluate(dataset, expr.rhs)
        lhs = evaluate(dataset, expr.lhs)
        assert isinstance(rhs, VarData)
        assert isinstance(lhs, VarData)
        
        dataframe = rhs.dataframe[rhs.dataframe != lhs.dataframe]
        metadata = rhs.metadata
        return VarData(dataframe, metadata)

    elif isinstance(expr, LessThan):
        rhs = evaluate(dataset, expr.rhs)
        lhs = evaluate(dataset, expr.lhs)
        assert isinstance(rhs, VarData)
        assert isinstance(lhs, VarData)

        dataframe = None
        metadata = rhs.metadata
        
        if (not rhs.metadata):
            raise ValueError('Malformed Relation. Filter on Variables must have variable as rhs')
        elif (rhs.metadata['dtype'] == DataType.NOMINAL):
            raise ValueError('Cannot compare nominal values with Less Than')
        elif (rhs.metadata['dtype'] == DataType.ORDINAL):
            comparison = lhs.dataframe[0]
            if (isinstance(comparison, str)):
                categories = lhs.metadata['categories'] # OrderedDict
                dataframe = filter(lambda x: categories[x] < categories[comparison], rhs.dataframe)

            elif (isinstance(comparison, int)):
                categories = lhs.metadata['categories'] # OrderedDict
                dataframe = filter(lambda x: categories[x] < comparison, rhs.dataframe)

            else: 
                raise ValueError(f"Cannot compare ORDINAL variables to {type(lhs.dataframe[0])}")

            return VarData(dataframe, metadata)

        elif (rhs.metadata['dtype'] == DataType.INTERVAL or rhs.metadata['dtype'] == DataType.RATIO):
            dataframe = filter(lambda x: x < comparison, rhs.dataframe) # TODO check return type and index if pandas Series
            
        else:
            raise Exception(f"Invalid Less Than Operation:{rhs} < {lhs}")

    elif isinstance(expr, LessThanEqual):
        # Could implement with Less Than and Equal
        raise Exception('Not implemented LESS THAN EQUAL')
    
    
    
    elif isinstance(expr, GreaterThan):
        raise Exception('Not implemented GREATER THAN')
    
    elif isinstance(expr, GreaterThanEqual):
        raise Exception('Not implemented GREATER THAN EQUAL')

    elif isinstance(expr, Relate): 
        raise Exception('Not implemented RELATE')

    elif isinstance(expr, Compare): 
        raise Exception('Not implemented COMPARE')
    
    elif isinstance(expr, Add): 
        raise Exception('Not implemented Add')

    # TODO all the other arithmetic....

# def isnormal(data): 
#     return 

# helper method
def bootstrap():
    raise Exception('Not implemented BOOTSTRAP')


# More USER FACING
# Takes all evaluated results, stores for call and then outputs the results in a dictionary/table
def eval(dataset, args*):
    results = {}
    for e in args*: 
        results[e] = evaluate(dataset, expr)
    
    return eval 