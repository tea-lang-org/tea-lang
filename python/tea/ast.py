import attr
import os
import csv
import pandas as pd
import numpy as np

from enum import Enum
from typing import Dict, Union
from collections import OrderedDict
from pandas.api.types import CategoricalDtype

class Node(object):
    pass

class DataType(Enum):  
    ORDINAL = 0
    NOMINAL = 1
    INTERVAL = 2 # for CALCULATIONS, INTERVAL vs. RATIO data is not important distinction
    RATIO = 3 # for INTERPRETATIONS, important distinction

@attr.s
class Variable(Node): 
    name = attr.ib()  
    dtype = attr.ib()
    categories = attr.ib(default=None)
    drange = attr.ib(default=None)

    # def set_type(self, new_type): 
    #     if (new_type == 'ordinal'): 
    #         self.data_type = DataType.ORDINAL
    #     elif (new_type == 'nominal'): 
    #         self.data_type = DataType.NOMINAL
    #     elif (new_type == 'interval'): 
    #         self.data_type = DataType.INTERVAL
    #     elif (new_type == 'ratio'): 
    #         self.data_type = DataType.RATIO
    #     else: 
    #         raise Exception('Variables must be specified as being ordinal, nominal, interval, or ratio')
    
    # def set_order(self, new_order): 
    #     self.order = new_order

    # def set_categories(self, new_categories): 
    #     self.categories = new_categories


@attr.s(auto_attribs=True)
class Mean(Node): 
    var: Node 

@attr.s(auto_attribs=True)
class Median(Node): 
    var: Node

@attr.s(auto_attribs=True)
class StandardDeviation(Node): 
    var: Node

@attr.s(auto_attribs=True)
class Variance(Node): 
    var: Node

@attr.s(auto_attribs=True)
class Kurtosis(Node): 
    var: Node

@attr.s(auto_attribs=True)
class Skew(Node): 
    var: Node

@attr.s(auto_attribs=True)
class Normality(Node): 
    var: Node

@attr.s(auto_attribs=True)
class Frequency(Node):
    var: Node


@attr.s(auto_attribs=True)
class BinaryRelation(Node):
    lhs: Node
    rhs: Node

    def __le__(self, other):
        return LessThanEqual(self, other)
    
    def __lt__(self, other):
        return LessThan(self, other)
    
    def __ge__(self, other):
        return GreaterThanEqual(self, other)
    
    def __gt__(self, other):
        return GreaterThan(self, other)

    def __eq__(self, other):
        return Equal(self, other)

    def __ne__(self, other):
        return NotEqual(self, other)


class LessThanEqual(BinaryRelation):
    pass

class LessThan(BinaryRelation):
    pass

class GreaterThanEqual(BinaryRelation):
    pass

class GreaterThan(BinaryRelation):
    pass

class Equal(BinaryRelation):
    pass

class NotEqual(BinaryRelation):
    pass


@attr.s(auto_attribs=True)
class Experiment(Node):
    between: Node
    within: Node

@attr.s(auto_attribs=True)
class Model(Node):
    dep_var: Node
    indep_var: Node
    expr: Experiment

@attr.s(auto_attribs=True)
class Hypothesis(Node):
    model: Model
    prediction: BinaryRelation ## NOT SURE IF THIS IS WHAT WE WANT 

# class Value(Node):
#     value: Union[int, float, str]




