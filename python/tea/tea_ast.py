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

class DataType(Enum):  
    ORDINAL = 0
    NOMINAL = 1
    INTERVAL = 2 # for CALCULATIONS, INTERVAL vs. RATIO data is not important distinction
    RATIO = 3 # for INTERPRETATIONS, important distinction

@attr.s(init=False)
class Variable(object): 
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


@attr.s(init=False)
class Dataset(object): 
    # variables: list
    # variable_names: list
    # data: list

    def __init__(self, data=None, variable_names=None, variables=None): 
        self.variables = None
        self.variable_names = None
        self.data = None

    def load_data(self, source_name):
        source_path = BASE_PATH + '/Datasets/' + source_name
        data = pd.read_csv(source_path)

        # Check that each column has a unique variable name
        variable_names = data.columns.values.tolist()

        # There are duplicates
        if (len(variable_names) != len(set(variable_names))):
            seen = set()
            duplicates = dict()
            for v in variable_names:
                if v not in seen:
                    seen.add(v)
                else:  #already seen
                    duplicates.append(v)
                    dup_counts.append(1)
                
            # TODO: Raise error here for duplicates!
            raise Exception('Duplictes! - may want to pass to pretty print warning/error')

            duplicates = []
        else:  # Only assign data to dataset if there are not variable name collisions
            self.data = data
            self.variable_names = variable_names
            self.variables = list()
    
    def initialize_variables(self, order): 
        pass
    
    def set_variable(self, var_name, var_type, var_categories=None): 
        # assert(var_name in self.variable_names)
        var = Variable(var_name, var_type, var_categories)
        self.variables.append(var)

    def get_variable(self, var_name): 
        assert(var_name in self.variable_names)
        
        var_data = self.data[var_name]
        idx = [i for i,v in enumerate(self.variables) if (v.name == var_name)].pop()
        var_type = self.variables[idx].data_type

        if (var_type == DataType.INTERVAL or var_type == DataType.RATIO): 
            var_data = pd.to_numeric(var_data)
        else: 
            var_data = [str(d) for i,d in enumerate(var_data)]
        return (self.variables[idx], var_data)
        
# @attr.s(auto_attribs=True)
# class Test(object): 
#     independent_variable: Variable
#     dependent_variable: Variable


@attr.s(auto_attribs=True)
class UnivariateTest(object): 
    # dependent_variable: None # Do we need this??

    def mean(var: Variable): 
        # assert(var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO)

        if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
            return Mean(var)
        elif (var.data_type == DataType.ORDINAL): 
            return Mean_Ordinal(var)
        else: 
            raise Exception ('Cannot take mean of NOMINAL data!')

    def median(var: Variable): 
        if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
            return Median(var)
        elif (var.data_type == DataType.ORDINAL): 
            return Median_Ordinal(var)
        else: 
            raise Exception ('Cannot take median of NOMINAL data!')
        

    def std_dev(var: Variable): 
        if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
            return StandardDeviation(var)
        elif (var.data_type == DataType.ORDINAL): 
            return StandardDeviation_Ordinal(var)
        else: 
            raise Exception ('Cannot calculate standard deviation of NOMINAL data!')

    def variance(var: Variable): 
        if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
            return Variance(var)
        elif (var.data_type == DataType.ORDINAL): 
            return Variance_Ordinal(var)
        else: 
            raise Exception ('Cannot calculate variance of NOMINAL data!')

    def kurtosis(var: Variable): 
        if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
            return Kurtosis(var)
        elif (var.data_type == DataType.ORDINAL): 
            return Kurtosis_Ordinal(var)
        else: 
            raise Exception ('Cannot calculate kurtosis of NOMINAL data!') # TODO??????

    def skew(var: Variable): 
        if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
            return Skew(var)
        elif (var.data_type == DataType.ORDINAL): 
            return Skew_Ordinal(var)
        else: 
            raise Exception ('Cannot calculate kurtosis of NOMINAL data!') # TODO??????
    
    def normality(var: Variable): 
        if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
            return Normality(var)
        elif (var.data_type == DataType.ORDINAL): 
            return Normality_Ordinal(var)
        else: 
            raise Exception ('Cannot calculate normality (kurtosis, skew) of NOMINAL data!') # TODO??????

    # Could be called on numeric and categorical data types
    def frequency(var:Variable):
        # May want to use Pandas (https://pandas.pydata.org/pandas-docs/stable/categorical.html#description)
        if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
            return Frequency(var)
        else: # DataType.NOMINAL or DataType.ORDINAL
            return Frequency_Categorical(var)
        

@attr.s(auto_attribs=True)
class Mean(UnivariateTest): 
    var: Variable

@attr.s(auto_attribs=True)
class Mean_Ordinal(UnivariateTest): 
    var: Variable

@attr.s(auto_attribs=True)
class Median(UnivariateTest): 
    var: Variable

@attr.s(auto_attribs=True)
class Median_Ordinal(UnivariateTest): 
    var: Variable
 
@attr.s(auto_attribs=True)
class StandardDeviation(UnivariateTest): 
    var: Variable

@attr.s(auto_attribs=True)
class StandardDeviation_Ordinal(UnivariateTest): 
    var: Variable

@attr.s(auto_attribs=True)
class Variance(UnivariateTest): 
    var: Variable

@attr.s(auto_attribs=True)
class Variance_Ordinal(UnivariateTest): 
    var: Variable

@attr.s(auto_attribs=True)
class Kurtosis(UnivariateTest): 
    var: Variable

@attr.s(auto_attribs=True)
class Kurtosis_Ordinal(UnivariateTest): 
    var: Variable

@attr.s(auto_attribs=True)
class Skew(UnivariateTest): 
    var: Variable

@attr.s(auto_attribs=True)
class Skew_Ordinal(UnivariateTest): 
    var: Variable

@attr.s(auto_attribs=True)
class Normality(UnivariateTest): 
    var: Variable

@attr.s(auto_attribs=True)
class Normality_Ordinal(UnivariateTest): 
    var: Variable

@attr.s(auto_attribs=True)
class Frequency(UnivariateTest):
    var: Variable

@attr.s(auto_attribs=True)
class Frequency_Categorical(UnivariateTest):
    var: Variable




@attr.s(auto_attribs=True)
class BivariateTest(object): 
    pass



Test = Union[UnivariateTest, BivariateTest]



@attr.s(auto_attribs=True)
class Quantity(object):
    var: Union[str, int, float]

@attr.s(auto_attribs=True)
class Relation(object):
    # lhs: Quantity
    # rhs: Quantity

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


class LessThanEqual(Relation):
    lhs: Variable
    rhs: Quantity

class LessThan(Relation):
    lhs: Variable
    rhs: Quantity

class GreaterThanEqual(Relation):
    lhs: Variable
    rhs: Quantity

class GreaterThan(Relation):
    lhs: Variable
    rhs: Quantity

class Equal(Relation):
    lhs: Variable
    rhs: Quantity

class NotEqual(Relation):
    lhs: Variable
    rhs: Quantity



# import pdb; pdb.set_trace()