from typing import Dict
from collections import OrderedDict
from .ast import (Variable, DataType, Literal)
# , DataType, Mean, Median, StandardDeviation, Variance, Kurtosis, Skew, Normality, Frequency,
                # Experiment, Model, Equation, Hypothesis, Relation,
                # Experiment_SetUp)
from .dataset import Dataset 
# from .evaluate import evaluate, pretty_print

def const(val: Literal):
    return Literal(val)

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
    return Variable.from_spec(var_name, DataType.NOMINAL, categories, None)

# def interval(var_name: str, range: list):
#     return Variable.from_spec(var_name, DataType.INTERVAL, None, range) # treat range like categories, check that all values are within range

# def ratio(var_name: str, range: list):
#     return Variable.from_spec(var_name, DataType.RATIO, None, range) # treat range like categories, check that all values are within range

# @param pid is the name of the column with participant ids
def load_data(source_name: str, vars: list, pid: str):
    return Dataset(source_name, vars, pid)

def filter(var: Variable, op: str, other: Literal): 
    if (op == '=='):
        return var.subset_equals(other)
    elif (op == '!='):
        pass
    elif (op == '>'):
        pass
    elif (op == '>='):
        pass
    elif (op == '<'):
        pass
    elif (op == '<='):
        pass
    else: 
        raise ValueError(f"Do not support the operator{op}")

# def load_data_arrs(y: list, x: list):
#     return Dataset.from_arr_numeric(y, x)

# def mean(var: Variable): 
#     return Mean(var)

# def median(var: Variable): 
#     return Median(var)

# def standard_deviation(var: Variable): 
#     return StandardDeviation(var)

# def variance(var: Variable): 
#     return Variance(var)

# def kurtosis(var: Variable): 
#     return Kurtosis(var)

# def skew(var: Variable): 
#     return Skew(var)

# def normality(var: Variable): 
#     return Normality(var)

# def frequency(var: Variable): 
#     return Frequency(var)
    
# def between_experiment(between_vars: list):
#     return Experiment(ExperimentType.BETWEEN_SUBJECTS, between_vars, None)

# def within_experiment(within_vars: list):
#     return Experiment(ExperimentType.WITHIN_SUBJECTS, None, within_vars)

# def mixed_experiment(between_vars: list, within_vars: list):
#     return Experiment(ExperimentType.MIXED, between_vars, within_vars)    

# # def experiment(exp_type: ExperimentType, between_vars: list, within_vars: list):
# #     return Experiment(exp_type, between_vars, within_vars)

# def equation(eq):
#     return Equation(eq)

# # @param indep_var is a list of Variables
# def model(dep_var: Variable, eq_indep_vars: Variable):
#     return Model(dep_var, eq_indep_vars)

# def hypothesis(prediction: Relation):
#     return Hypothesis(prediction)

# def experiment_design(variables: tuple):
#     return Experiment_SetUp(variables)

# # TODO may need to use this for within subjects analysis
# def form_groups(var: Variable, bins):
#     pass

# def check_bin(var: Variable, bin: tuple):
#     # should do some sort of type checking for the bin indices, assert that they are the correct type?

#     # raise Exception if bin is invalid
#     pass

# # @params bins is a list of tuples representing different bins
# # @returns list of new variables
# def make_new_variables(var: Variable, bins: list):
#     new_vars = list

#     for i,b in enumerate(bins): 
#         check_bin(var, b)
        
#         # name the variable ??
#         new_vars.append(Variable(var.name + str(i), var.dtype, var.categories, var.drange))

#     # return list of new variables
#     return  new_vars

# # # Helper -- should make private? 
# # def get_dataset(dataset_name: str) -> Dataset: 
# #     if (dataset_name not in globals()): 
# #         raise Exception('Dataset does not exist!') # Have some nicer error message
    
# #     return globals()[dataset_name]


# # def groups(dataset: Dataset, variable: Variable, sub_groups: Dict[str, Relation]=None): 
# #     # if isinstance()
# #     if (sub_groups): 
# #         pass
# #             # check_value_exists()
# #             # calculate the values
# #     else: 
# #         pass