from typing import Dict, Union
from collections import OrderedDict
from .ast import (  Variable, DataType, Literal,
                    Compare
                )
from .dataset import Dataset 

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

# TODO: Likely need to change the signature of this method
def predict(iv: Variable, dv: Variable, prediction: str): 
    # TODO: need to check that the prediction is well-formed (VALUES that are ordered exist, for example)
    if (prediction):
        if(isnominal(iv) or isordinal(iv)): 
            if ('<' in prediction):
                lhs = prediction[:prediction.index('<')].strip()
                rhs = prediction[prediction.index('<')+1:].strip()
                assert(lhs in iv.categories.keys())
                assert(rhs in iv.categories.keys())
                return [const(lhs) < const(rhs)]

            elif ('>' in prediction):
                lhs = prediction[:prediction.index('>')].strip()
                rhs = prediction[prediction.index('>')+1:].strip()
                assert(lhs in iv.categories.keys())
                assert(rhs in iv.categories.keys())
                return [const(lhs) > const(rhs)]

            elif ('==' in prediction):
                lhs = prediction[:prediction.index('==')].strip()
                rhs = prediction[prediction.index('==')+1:].strip()
                assert(lhs in iv.categories.keys())
                assert(rhs in iv.categories.keys())
                return [const(lhs) == const(rhs)]
            
            elif ('=' in prediction): # in case user wants to use single equals
                lhs = prediction[:prediction.index('=')].strip()
                rhs = prediction[prediction.index('=')+1:].strip()
                assert(lhs in iv.categories.keys())
                assert(rhs in iv.categories.keys())
                return [const(lhs) == const(rhs)]

            elif ('!=' in prediction):
                lhs = prediction[:prediction.index('!=')].strip()
                rhs = prediction[prediction.index('!=')+1:].strip()
                assert(lhs in iv.categories.keys())
                assert(rhs in iv.categories.keys())
                return [const(lhs) != const(rhs)]

            else: 
                raise ValueError(f"{prediction}: Trying to use a comparison operator that is not supported for IV of type {iv.dtype}!\nThe following are supported: <, >, ==, !=")
        elif (isnumeric(iv)): 
            if ('~' in prediction): 
                lhs = prediction[:prediction.index('~')].strip()
                rhs = prediction[prediction.index('~')+1:].strip()

                # if ('-')
            elif ('<' in prediction):
                # raise NotImplementedError
                lhs = prediction[:prediction.index('<')].strip()
                rhs = prediction[prediction.index('<')+1:].strip()
                return [const(lhs) < const(rhs)]
            elif ('>' in prediction):
                raise NotImplementedError
            elif ('==' in prediction): 
                raise NotImplementedError
            elif ('!=' in prediction): 
                raise NotImplementedError
            else: 
                raise ValueError(f"{prediction}: Trying to use a comparison operator that is not supported for IV of type {iv.dtype}!\nThe following are supported: <, >, ==, !=")
                
            

                


# @params: iv could be the list of variables/groups want to compare on dv - may only want to compare 2 groups, not all conditions
def compare(iv, dv, prediction:str=None, when:str=None) :
    # iv_var = iv
    # dv_var = dv 
    # if (isinstance(iv, str)):
    #     iv_var = 
    if (isinstance(iv, Variable)):
        if isnominal(iv) or isordinal(iv):
            return Compare(iv, dv, predict(iv, dv, prediction))
        elif isnumeric(iv):
            return Compare(iv, dv, predict(iv, dv, prediction))
        else: 
            raise ValueError(f"Invalid Variable type: {iv.dtype}")
    else: # iv is already a list of Variables
            return Compare(iv, dv)

# def compare(var, var, semantically_same=True): # Compare two groups
#     pass

# compare(iv, dv, predictions)
# compare(dv, dv, groups=False) or compare (iv, iv, groups=False) 
# # Are they the same groups? 

# strategy = nominal('strategy', ['forking', 'caching', 'naive'])
# ratio('time', drange=[0, 10000], comes_from=(strategy, ['forking', 'caching', 'naive']))