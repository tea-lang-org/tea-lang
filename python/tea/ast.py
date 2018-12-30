import attr
import os
import csv
import pandas as pd
import numpy as np

from enum import Enum
from typing import Dict, Union
from collections import OrderedDict
from pandas.api.types import CategoricalDtype
# from attr import attrs, attrib

class Node(object):
    pass

class Eq_Node(Node):
    def __add__(self, other):
        return Add(self, other)

    def __sub__(self, other):
        return Sub(self, other)

    def __mul__(self, other):
        return Mul(self, other)

    def div(self, other):
        return Div(self, other)

class DataType(Enum):  
    ORDINAL = 0
    NOMINAL = 1
    INTERVAL = 2 # for CALCULATIONS, INTERVAL vs. RATIO data is not important distinction
    RATIO = 3 # for INTERPRETATIONS, important distinction

@attr.s
class Variable(Eq_Node): 
    # name = attr.ib(type=str)
    # dtype = attr.ib(type=DataType)
    # categories = attr.ib(type=list)
    # drange = attr.ib(type=list)

    name = attr.ib()
    dtype = attr.ib()
    categories = attr.ib()
    drange = attr.ib()

    @classmethod
    def from_spec(cls, name: str, dtype: DataType, cat: list=None, drange: list=None):
        return cls(name, dtype, cat, drange)
    
@attr.s(hash=True)
class Add(Eq_Node): 
    rhs = attr.ib(type=Variable)
    lhs = attr.ib(type=Variable)

@attr.s(hash=True)
class Sub(Eq_Node): 
    rhs = attr.ib(type=Node)
    lhs = attr.ib(type=Node)

@attr.s(hash=True)
class Mul(Eq_Node): 
    rhs = attr.ib(type=Node)
    lhs = attr.ib(type=Node)

@attr.s(hash=True)
class Div(Eq_Node): 
    rhs = attr.ib(type=Node)
    lhs = attr.ib(type=Node)

@attr.s(auto_attribs=False, hash=True)
class Equation(Node):
    eq_handle = attr.ib(type=Eq_Node)
    # rhs = attr.ib(type=Node)
    # op = attr.ib(type=Node)
    # lhs = attr.ib(type=Node)


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


class ExperimentType(Enum): # May not need this
    BETWEEN_SUBJECTS = 0
    WITHIN_SUBJECTS = 1
    MIXED = 2

@attr.s(auto_attribs=True)
class Experiment(Node):
    exper_type: ExperimentType
    between_vars: list
    within_vars: list

    def __attrs_post_init__(self):
        if self.between_vars: # check that all elements in list are Variables
            for bv in self.between_vars:
                if not isinstance(bv, Variable):
                    raise Exception(f"Between subjects variable list: NOT of type Variable: {bv}")
        if self.within_vars: # check that all elements in list are Variables
            for wv in self.within_vars:
                if not isinstance(wv, Variable):
                    raise Exception(f"Within subjects variable list: NOT of type Variable: {wv}")


@attr.s(auto_attribs=True)
class Model(Node):
    dependent_var: Variable
    eq_independent_vars: Equation # User-facing: list of vars or equation (both should be allowed)
    experiment: Experiment

@attr.s(auto_attribs=True)
class Hypothesis(Node):
    model: Model
    prediction: BinaryRelation ## NOT SURE IF THIS IS WHAT WE WANT 

# class Value(Node):
#     value: Union[int, float, str]