from typing import Dict, Union
from collections import OrderedDict
from .ast import (  Variable, DataType, Literal,
                    Relate, Relationship
                )
from .dataset import Dataset 

iv_identifier = 'independent variable'
dv_identifier = 'dependent variable'
var_identifier = 'variable'

def const(val):
    return Literal(val)

def ordinal(var_name: str, ordered_categories: list):
    # Create order tuple
    categories = OrderedDict()
    for i, c in enumerate(ordered_categories):
        categories[c] = i+1 # start at 1 not 0
        
    return Variable.from_spec(var_name, DataType.ORDINAL, categories, [1, len(categories)])

def isordinal(var: Variable):
    return var.dtype is DataType.ORDINAL

def nominal(var_name: str, unordered_categories: list):
    categories = OrderedDict()
    for i, c in enumerate(unordered_categories):
        categories[c] = -1
    return Variable.from_spec(var_name, DataType.NOMINAL, categories, None)

def isnominal(var: Variable):
    return var.dtype is DataType.NOMINAL

def interval(var_name: str, drange: list=None):
    return Variable.from_spec(var_name, DataType.INTERVAL, None, drange) # treat range like categories, check that all values are within range

def isinterval(var: Variable):
    return var.dtype is DataType.INTERVAL

def ratio(var_name: str, drange: list=None):
    return Variable.from_spec(var_name, DataType.RATIO, None, drange) # treat range like categories, check that all values are within range

def isratio(var: Variable):
    return var.dtype is DataType.RATIO

def isnumeric(var: Variable):
    return (isratio(var) or isinterval(var))

# @param pid is the name of the column with participant ids
def load_data(source_name: str, vars: list, pid: str):
    return Dataset(source_name, vars, pid)

def select(var: Variable, op: str, other: Literal): 
    if (op == '=='):
        return var.subset_equals(other)
    elif (op == '!='):
        return var.subset_not_equals(other)
    elif (op == '<'):
        return var.subset_lt(other)
    elif (op == '<='):
        return var.subset_le(other)
    elif (op == '>'):
        return var.subset_gt(other)
    elif (op == '>='):
        return var.subset_ge(other)
    else: 
        raise ValueError(f"Do not support the operator{op}")

# @param vars: list of all vars in tuple form (Variable, 'iv/dv/variable')
# @param role: "role" of Variable (i.e., independent variable, dependent variable, variable)
# @returns new list of vars with specified role
# def get_vars(role: str, vars: list): 
#     vars_role = []
#     for v,r in vars:
#         if r == role: 
#             vars_role.append(v)
    
#     return vars_role

# TODO: need to check that the prediction is well-formed (VALUES that are ordered exist, for example)
"""
    Grammar for predictions: 
    # Cat x Numeric
    # what matters is that the var using to form groups in comparison is nominal/categorical 
    <, >, ==, != --> Tests null hypothesis that there is no difference OR ask for one-sidedness in tests (as constraint?)
    predict(groups: Variable, outcome: Variable, prediction: str=None)
    # Cat x Cat
    Frequency(??)
    predict(groups: Variable, outcome: Variable, prediction: str=None)
    # Numeric x Cat
    # we need to know which variable is factor vs. predictor
    logistic regression
    predict(var: Variable, outcome: Variable, prediction: str=None)
    # Numeric x Numeric --> Should allow for both
    # Need to know which variable is factor vs predictor
    Prediction: y ~ - var + var + var (e.g., time ~ + condition + age || prediction: condition:a > condition:b)
    Prediction: + var, - var
    predict(outcome: Variable, factors: list of variables, prediction: str=None)
    predict(factors: list, outcome: Variable, prediction: str=None)
    --> check type of outcome
    --> check number of factors: if > 1 then multivariate case else bivariate case, check for factor type
    --> in multivariate case, the types of factors don't have a bearing on the ....?
"""
def predict(factors: list, outcome: Variable, prediction: str=None):    
    global iv_identifier

    if (prediction):
        if (len(factors) == 1): # Bivariate case
            factor = factors[0]
            if(isnominal(factor) or isordinal(factor)): 
                # TODO: Should the below change if Outcome is Cat or Numeric???
                if ('<' in prediction):
                    lhs = prediction[:prediction.index('<')].strip()
                    rhs = prediction[prediction.index('<')+1:].strip()
                    assert(lhs in factor.categories.keys())
                    assert(rhs in factor.categories.keys())
                    return [const(lhs) < const(rhs)]

                elif ('>' in prediction):
                    lhs = prediction[:prediction.index('>')].strip()
                    rhs = prediction[prediction.index('>')+1:].strip()
                    assert(lhs in factor.categories.keys())
                    assert(rhs in factor.categories.keys())
                    return [const(lhs) > const(rhs)]

                elif ('==' in prediction):
                    lhs = prediction[:prediction.index('==')].strip()
                    rhs = prediction[prediction.index('==')+1:].strip()
                    assert(lhs in factor.categories.keys())
                    assert(rhs in factor.categories.keys())
                    return [const(lhs) == const(rhs)]
                
                elif ('=' in prediction): # in case user wants to use single equals
                    lhs = prediction[:prediction.index('=')].strip()
                    rhs = prediction[prediction.index('=')+1:].strip()
                    assert(lhs in factor.categories.keys())
                    assert(rhs in factor.categories.keys())
                    return [const(lhs) == const(rhs)]

                elif ('!=' in prediction):
                    lhs = prediction[:prediction.index('!=')].strip()
                    rhs = prediction[prediction.index('!=')+1:].strip()
                    assert(lhs in factor.categories.keys())
                    assert(rhs in factor.categories.keys())
                    return [const(lhs) != const(rhs)]

                else: 
                    raise ValueError(f"{prediction}: Trying to use a comparison operator that is not supported for IV of type {factor.dtype}!\nThe following are supported: <, >, ==, !=")
            
            elif (isnumeric(factor)): 
                # TODO: Should the below change if Outcome is Cat or Numeric???
                if ('~' in prediction): 
                    lhs = prediction[:prediction.index('~')].strip()
                    rhs = prediction[prediction.index('~')+1:].strip()

                    if ('-' in lhs): # "as LHS decreases,..."
                        lhs = lhs[lhs.index('-')+1:]
                        if ('-' in rhs): # "as RHS decreases,..."
                            rhs = rhs[rhs.index('-')+1:]
                            return [Relationship(lhs).positive(Relationship(rhs))]
                        else: # "as RHS increases,..."
                            rhs = rhs[rhs.index('+')+1:]
                        return [Relationship(lhs).negative(Relationship(rhs))]
                    else: # "as LHS increases,..."
                        lhs = lhs[lhs.index('+')+1:]
                        if ('-' in rhs): # "as RHS decreases,..."
                            rhs = rhs[rhs.index('-')+1:]
                            return [Relationship(lhs).negative(Relationship(rhs))]
                        else: # "as RHS increases,..."
                            rhs = rhs[rhs.index('+')+1:]
                        return [Relationship(lhs).positive(Relationship(rhs))]
                    # Multivariate case?: if there is a categorical variable as an iV,can allow for : access on groups (e.g., condition:a > condition:b)

                # else: 
                    # raise ValueError(f"{prediction}: Trying to use a comparison operator that is not supported for IV of type {iv.dtype}!\nThe following are supported: <, >, ==, !=")
        elif (len(factors) > 1): # Multivariate analysis 
            raise NotImplementedError
            
# Generic interface for observing relationships among variables (observational studies and experiments)
# @params: vars should be a list of Variables
def relate(vars: list, prediction: str=None) : 
    # ivs = vars['iv']
    # dv = vars['dv']
    # assert (len(dv) == 1)
    return Relate(vars, predict(vars, prediction))

# @params: iv could be the list of variables/groups want to compare on dv - may only want to compare 2 groups, not all conditions
# def compare(var_1: Variable, var_2: Variable, prediction: str=None, when: str=None) :

def compare(iv: Variable, dv: Variable, prediction: str=None, when: str=None) :
    
    # vars = [(var_1, 'variable'), (var_2, 'variable')]
    return Relate([iv, dv], predict([iv], dv, prediction))
    
    # if (isinstance(iv, Variable)):
    #     vars = [(iv, iv_identifier), (dv, dv_identifier)]
    #     if isnominal(iv) or isordinal(iv):
    #         return Relate(vars, predict(vars, prediction))
    #     elif isnumeric(iv):
    #         return Relate(vars, predict(vars, prediction))
    #     else: 
    #         raise ValueError(f"Invalid Variable type: {iv.dtype}")
    # elif (isinstance(iv, list)): 
    #     vars = []
    #     for i in iv: 
    #         vars.append((i, iv_identifier))
    #     return Relate(vars, predict(vars, prediction))
    # else: 
    #     raise ValueError (f"IV (first parameter) is not a Variable or list of Variables: {f.type}")

# def compare(var, var, semantically_same=True): # Compare two groups
#     pass

# compare(iv, dv, predictions)
# compare(dv, dv, groups=False) or compare (iv, iv, groups=False) 
# # Are they the same groups? 

# strategy = nominal('strategy', ['forking', 'caching', 'naive'])
# ratio('time', drange=[0, 10000], comes_from=(strategy, ['forking', 'caching', 'naive']))