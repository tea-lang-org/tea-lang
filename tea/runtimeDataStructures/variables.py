from tea.ast import (  Variable, DataType, Literal,
                    Relate, Relationship
                )

from typing import Dict, Union
from collections import OrderedDict

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

def iscategorical(var: Variable):
    return (isnominal(var) or isordinal(var))