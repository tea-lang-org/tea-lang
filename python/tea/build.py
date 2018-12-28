from typing import Dict
from collections import OrderedDict
from .ast import (Variable, DataType, Mean, Median, StandardDeviation, Variance, Kurtosis, Skew, Normality, Frequency,
                Experiment, ExperimentType, Model)
from .dataset import Dataset 
# from .evaluate import evaluate, pretty_print

def ordinal(var_name: str, ordered_categories: list):
    # Create order tuple
    categories = OrderedDict()
    for i, c in enumerate(ordered_categories):
        categories[c] = i+1 # start at 1 not 0
        
    return Variable.from_spec(var_name, DataType.ORDINAL, categories, [1, len(categories)])
    # return Variable(var_name, DataType.ORDINAL, categories, [1, len(categories)])

def nominal(var_name: str, unordered_categories: list):
    categories = OrderedDict()
    for i, c in enumerate(unordered_categories):
        categories[c] = -1
    return Variable(var_name, DataType.NOMINAL, categories, drange=None)

def interval(var_name: str, range: list):
    return Variable(var_name, DataType.INTERVAL, categories=None, drange=range) # treat range like categories, check that all values are within range

def ratio(var_name: str, range: list):
    return Variable(var_name, DataType.RATIO, categories=None, drange=range) # treat range like categories, check that all values are within range

def load_data(source_name: str, vars: list):
    return Dataset(source_name, vars)

def mean(var: Variable): 
    return Mean(var)

def median(var: Variable): 
    return Median(var)

def standard_deviation(var: Variable): 
    return StandardDeviation(var)

def variance(var: Variable): 
    return Variance(var)

def kurtosis(var: Variable): 
    return Kurtosis(var)

def skew(var: Variable): 
    return Skew(var)

def normality(var: Variable): 
    return Normality(var)

def frequency(var: Variable): 
    return Frequency(var)
    
def between_experiment(between_vars: list):
    return Experiment(ExperimentType.BETWEEN_SUBJECTS, between_vars, None)

def within_experiment(within_vars: list):
    return Experiment(ExperimentType.WITHIN_SUBJECTS, None, within_vars)

def mixed_experiment(between_vars: list, within_vars: list):
    return Experiment(ExperimentType.MIXED, between_vars, within_vars)    

# def experiment(exp_type: ExperimentType, between_vars: list, within_vars: list):
#     return Experiment(exp_type, between_vars, within_vars)

# @param indep_var is a list of Variables
def model(dep_var: Variable, indep_vars: Variable, exper: Experiment):
    import pdb; pdb.set_trace()
    return Model(dep_var, indep_vars, exper)

# TODO may need to use this for within subjects analysis
def form_groups(var: Variable, bins):
    pass

def check_bin(var: Variable, bin: tuple):
    # should do some sort of type checking for the bin indices, assert that they are the correct type?

    # raise Exception if bin is invalid
    pass

# @params bins is a list of tuples representing different bins
# @returns list of new variables
def make_new_variables(var: Variable, bins: list):
    new_vars = list

    for i,b in enumerate(bins): 
        check_bin(var, b)
        
        # name the variable ??
        new_vars.append(Variable(var.name + str(i), var.dtype, var.categories, var.drange))

    # return list of new variables
    return  new_vars

# # Helper -- should make private? 
# def get_dataset(dataset_name: str) -> Dataset: 
#     if (dataset_name not in globals()): 
#         raise Exception('Dataset does not exist!') # Have some nicer error message
    
#     return globals()[dataset_name]


# def groups(dataset: Dataset, variable: Variable, sub_groups: Dict[str, Relation]=None): 
#     # if isinstance()
#     if (sub_groups): 
#         pass
#             # check_value_exists()
#             # calculate the values
#     else: 
#         pass