from typing import Dict, Union
from collections import OrderedDict
from .ast import (  Variable, DataType, Literal,
                    Compare
                )
# , DataType, Mean, Median, StandardDeviation, Variance, Kurtosis, Skew, Normality, Frequency,
                # Experiment, Model, Equation, Hypothesis, Relation,
                # Experiment_SetUp)
from .dataset import Dataset 
# from .evaluate import evaluate, pretty_print

def const(val):
    return Literal(val)

def ordinal(var_name: str, ordered_categories: list):
    # Create order tuple
    categories = OrderedDict()
    for i, c in enumerate(ordered_categories):
        categories[c] = i+1 # start at 1 not 0
        
    return Variable.from_spec(var_name, DataType.ORDINAL, categories, [1, len(categories)])
    # return Variable(var_name, DataType.ORDINAL, categories, [1, len(categories)])

def isordinal(var: Variable):
    return var.dtype is DataType.ORDINAL

def nominal(var_name: str, unordered_categories: list):
    categories = OrderedDict()
    for i, c in enumerate(unordered_categories):
        categories[c] = -1
    return Variable.from_spec(var_name, DataType.NOMINAL, categories, None)

def isnominal(var: Variable):
    return var.dtype is DataType.NOMINAL

def interval(var_name: str, drange: list):
    return Variable.from_spec(var_name, DataType.INTERVAL, None, drange) # treat range like categories, check that all values are within range

def isinterval(var: Variable):
    return var.dtype is DataType.INTERVAL

def ratio(var_name: str, drange: list):
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
def predict(iv: Variable, prediction: str): 
    
    if(iv.dtype is DataType.NOMINAL or iv.dtype is DataType.ORDINAL): 
        if ('>' in prediction):
            lhs = prediction[:prediction.index('>')].strip()
            rhs = prediction[prediction.index('>')+1:].strip()
            assert(lhs in iv.categories.keys())
            assert(rhs in iv.categories.keys())

            return const(lhs) > const(rhs)


    # need to check that the prediction is well-formed (VALUES that are ordered exist, for example)
    
        # lhs = prediction[:prediction.index(comparison)]
        # rhs = prediction[prediction.index(comparison)+1:]
        # assert(lhs in iv.categories)
        # assert(rhs in iv.categories)

        # return const(lhs) 


# X could be the list of variables/groups want to compare on y - may only want to compare 2 groups, not all conditions
def compare(iv, dv: Variable, prediction: str) :
    ivs = []
    if (isinstance(iv, Variable)):
        if isnominal(iv) or isordinal(iv):
            #split up based on categories, build ivs and then pass to Compare
            # groups = list(iv.categories.keys())
            # for g in groups: 
            #     ivs.append(select(iv, '==', const(g)))
            # import pdb; pdb.set_trace()
            return Compare(iv, dv, [predict(iv, prediction)])
        elif isnumeric(iv):
            # pass directly to Compare
            raise AssertionError('NOT IMPLEMENTED')
        else: 
            raise ValueError(f"Invalid Variable type: {iv.dtype}")
    else: # iv is already a list of Variables
        return Compare(iv, dv)
        # # For preprocessing in case we want to 
        # if isnumeric(x):
        #     if isnumeric(y):
        #         print('Need to implement how to do Numeric x Numeric')
        #     elif isnominal(y):
        #         print('Need to implement Numeric x Nominal')
        #     elif isordinal(y):
        #         print('Need to implement Numeric x ORDINAL - may be able to just call compare using numbers for categories') 
        #     else: 
        #         raise ValueError(f"Cannot have data of type{y.dtype}")
        # elif isnominal(x):
        #     raise ValueError('Not implemented! X is nominal')
        # elif isordinal(x):
        #     raise ValueError('Not implemented! X is ordinal')

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