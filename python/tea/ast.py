import attr
import os
import csv
import pandas as pd
import numpy as np

from enum import Enum
from typing import Dict, Union
from collections import OrderedDict
from pandas.api.types import CategoricalDtype


BASE_PATH = os.getcwd()

class Node(object):
    pass

class DataType(Enum):  
    ORDINAL = 0
    NOMINAL = 1
    INTERVAL = 2 # for CALCULATIONS, INTERVAL vs. RATIO data is not important distinction
    RATIO = 3 # for INTERPRETATIONS, important distinction

@attr.s(init=False)
class Variable(Node): 
    # data_type: DataType
    # order: list
    # categories: list

    def __init__(self, var_name: str, var_type: DataType, var_categories: OrderedDict): 
        self.name = var_name
        self.data_type = var_type
        self.categories = var_categories

    def set_type(self, new_type): 
        if (new_type == 'ordinal'): 
            self.data_type = DataType.ORDINAL
        elif (new_type == 'nominal'): 
            self.data_type = DataType.NOMINAL
        elif (new_type == 'interval'): 
            self.data_type = DataType.INTERVAL
        elif (new_type == 'ratio'): 
            self.data_type = DataType.RATIO
        else: 
            raise Exception('Variables must be specified as being ordinal, nominal, interval, or ratio')
    
    def set_order(self, new_order): 
        self.order = new_order

    def set_categories(self, new_categories): 
        self.categories = new_categories

        
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

class Value(Node):
    value: Union[int, float, str]


@attr.s(auto_attribs=True)
class BinaryRelation(object):
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

class LessThan(Relation):
    pass

class GreaterThanEqual(Relation):
    pass

class GreaterThan(Relation):
    pass

class Equal(Relation):
    pass

class NotEqual(Relation):
    pass

