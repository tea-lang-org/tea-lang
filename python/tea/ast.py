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
    def relate(self, other):
        return Relate(self, other)

    def compare(self, other):
        return Compare(self, other)
    
    def select(self, other):
        return Select(self, other)

    def __add__(self, other):
        return Add(self, other)

    def __sub__(self, other):
        return Sub(self, other)

    def __mul__(self, other):
        return Mul(self, other)

    def __truediv__(self, other):
        return Div(self, other)
    

    # MAY NOT NEED TO OVERRIDE AND, OR
    def __and__(self, other):
        return Add(self, other)
    
    def __or__(self, other):
        return Or(self, other)

@attr.s(repr=True)
class DataType(Enum):  
    ORDINAL = 0
    NOMINAL = 1
    # for CALCULATIONS, INTERVAL vs. RATIO data is not important distinction
    # for INTERPRETATIONS, important distinction (?)
    INTERVAL = 2 
    RATIO = 3

@attr.s(hash=True, repr=False)
class Variable(Node): 
    # meta data about the variable, determines how the operators are to be/can be executed
    name = attr.ib()
    dtype = attr.ib(type=DataType)
    categories = attr.ib()
    drange = attr.ib()
    
    # children from which self/this Variable is "derived"
    rhs = attr.ib(type=Node)
    lhs = attr.ib(type=Node)

    @classmethod
    def from_spec(cls, name: str, dtype: DataType, cat: list=None, drange: list=None, rhs: Node=None, lhs: Node=None):
        return cls(name, dtype, cat, drange, rhs, lhs)
    
    def subset_equals(self, other: Node):
        return Equal(self, other)
    
    def subset_not_equals(self, other: Node):
        return NotEqual(self, other)

    def subset_lt(self, other: Node):
        return LessThan(self, other)

    def subset_le(self, other: Node):
        return LessThanEqual(self, other)
    
    def subset_ge(self, other: Node):
        return GreaterThanEqual(self, other)
    
    def subset_gt(self, other: Node):
        return GreaterThan(self, other)

    def __repr__(self): 
        return self.name

@attr.s(hash=True, repr=False)
class Select(Node):
    var: Variable # variable to filter on
    condition: tuple # inclusive bounding on both sides
    
    def __repr__(self):
        return (f"Select {self.var} on [{self.condition}]")

@attr.s(hash=True, repr=False)
class Equal(Node):
    rhs = attr.ib(type=Node)
    lhs = attr.ib(type=Node)

@attr.s(hash=True, repr=False)
class NotEqual(Node):
    rhs = attr.ib(type=Node)
    lhs = attr.ib(type=Node)

@attr.s(hash=True, repr=False)
class LessThan(Node):
    rhs = attr.ib(type=Node)
    lhs = attr.ib(type=Node)

@attr.s(hash=True, repr=False)
class LessThanEqual(Node):
    rhs = attr.ib(type=Node)
    lhs = attr.ib(type=Node)

@attr.s(hash=True, repr=False)
class GreaterThan(Node):
    rhs = attr.ib(type=Node)
    lhs = attr.ib(type=Node)

@attr.s(hash=True, repr=False)
class GreaterThanEqual(Node):
    rhs = attr.ib(type=Node)
    lhs = attr.ib(type=Node)


# @attr.s(hash=True, repr=False)
# class Add(Eq_Node): 
#     rhs = attr.ib(type=Variable)
#     lhs = attr.ib(type=Variable)

#     def __repr__(self):
#         return f"{self.rhs} + {self.lhs}"

# @attr.s(hash=True, repr=False)
# class Sub(Eq_Node): 
#     rhs = attr.ib(type=Node)
#     lhs = attr.ib(type=Node)

#     def __repr__(self):
#         return f"{self.rhs} - {self.lhs}"

# @attr.s(hash=True, repr=False)
# class Mul(Eq_Node): 
#     rhs = attr.ib(type=Node)
#     lhs = attr.ib(type=Node)

#     def __repr__(self):
#         return f"{self.rhs} * {self.lhs}"

# @attr.s(hash=True, repr=False)
# class Div(Eq_Node): 
#     rhs = attr.ib(type=Node)
#     lhs = attr.ib(type=Node)

#     def __repr__(self):
#         return f"{self.rhs} / {self.lhs}"


# @attr.s(auto_attribs=False, hash=True, repr=False)
# class Equation(Node):
#     eq_handle = attr.ib(type=Eq_Node)
#     # rhs = attr.ib(type=Node)
#     # op = attr.ib(type=Node)
#     # lhs = attr.ib(type=Node)

#     def __repr__(self):
#         return repr(self.eq_handle)


# @attr.s(auto_attribs=True)
# class Mean(Node): 
#     var: Node 

# @attr.s(auto_attribs=True)
# class Median(Node): 
#     var: Node

# @attr.s(auto_attribs=True)
# class StandardDeviation(Node): 
#     var: Node

# @attr.s(auto_attribs=True)
# class Variance(Node): 
#     var: Node

# @attr.s(auto_attribs=True)
# class Kurtosis(Node): 
#     var: Node

# @attr.s(auto_attribs=True)
# class Skew(Node): 
#     var: Node

# @attr.s(auto_attribs=True)
# class Normality(Node): 
#     var: Node

# @attr.s(auto_attribs=True)
# class Frequency(Node):
#     var: Node


# TODO: Should definitely check that the values that are passed are correct/exist/legit
# Value = Union[Node, int, float, str] # Allow for Node but also for raw int/float/str values (from domain knowledge)

@attr.s(hash=True)
class Literal(Node):
    value = attr.ib(type=Union[int, float, str])

# @attr.s(auto_attribs=True)
# class Relation(Node):
#     lhs: Variable
#     rhs: Value

    # def __le__(self, other):
    #     return LessThanEqual(self, other)
    
    # def __lt__(self, other):
    #     return LessThan(self, other)
    
    # def __ge__(self, other):
    #     return GreaterThanEqual(self, other)
    
    # def __gt__(self, other):
    #     return GreaterThan(self, other)

    # def __eq__(self, other):
    #     return Equal(self, other)

    # def __ne__(self, other):
    #     return NotEqual(self, other)

# @attr.s(hash=True)
# class LessThanEqual(Relation):
#     rhs = attr.ib(type=Value) # Should be Value or Variable?
#     lhs = attr.ib(type=Value)

# class LessThan(Relation):
#     rhs = attr.ib(type=Value) # Should be Value or Variable?
#     lhs = attr.ib(type=Value)

# class GreaterThanEqual(Relation):
#     rhs = attr.ib(type=Value) # Should be Value or Variable?
#     lhs = attr.ib(type=Value)

# class GreaterThan(Relation):
#     rhs = attr.ib(type=Value) # Should be Value or Variable?
#     lhs = attr.ib(type=Value)


# class NotEqual(Relation):
#     rhs = attr.ib(type=Value) # Should be Value or Variable?
#     lhs = attr.ib(type=Value)

# # class Experiment_New(Node):
# #     grouping: Variable # Variable for which there are only 2 values, splitting the participants cleanly

# @attr.s(auto_attribs=True)
# class Experiment_SetUp(Node):
#     vars: list
     
# @attr.s(auto_attribs=True)
# class Experiment(Node):
#     between_vars: list
#     within_vars: list

#     def __attrs_post_init__(self):
#         if self.between_vars: # check that all elements in list are Variables
#             for bv in self.between_vars:
#                 if not isinstance(bv, Variable):
#                     raise Exception(f"Between subjects variable list: NOT of type Variable: {bv}")
#         if self.within_vars: # check that all elements in list are Variables
#             for wv in self.within_vars:
#                 if not isinstance(wv, Variable):
#                     raise Exception(f"Within subjects variable list: NOT of type Variable: {wv}")


# @attr.s(auto_attribs=True, hash=True, repr=False)
# class Model(Node):
#     dependent_var: Variable
#     eq_independent_vars: Equation # User-facing: list of vars or equation (both should be allowed)
#     # experiment: Experiment_SetUp

# @attr.s(auto_attribs=True)
# class Hypothesis(Node):
#     prediction: Relation ## NOT SURE IF THIS IS WHAT WE WANT 

# # class Value(Node):
# #     value: Union[int, float, str]
 