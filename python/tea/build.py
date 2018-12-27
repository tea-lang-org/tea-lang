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
        
    return Variable(var_name, DataType.ORDINAL, categories, [1, len(categories)])

def nominal(var_name: str, unordered_categories: list):
    categories = OrderedDict()
    for i, c in enumerate(unordered_categories):
        categories[c] = -1
    return Variable(var_name, DataType.NOMINAL, categories)

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

# def variable_list(vars: list):
#     return list(vars[0], vars[1:])

def between_experiment(between_vars: list):
    return Experiment(ExperimentType.BETWEEN_SUBJECTS, between_vars, None)

def within_experiment(within_vars: list):
    return Experiment(ExperimentType.WITHIN_SUBJECTS, None, within_vars)

def mixed_experiment(between_vars: list, within_vars: list):
    return Experiment(ExperimentType.MIXED, between_vars, within_vars)    

# def experiment(exp_type: ExperimentType, between_vars: list, within_vars: list):
#     return Experiment(exp_type, between_vars, within_vars)

# @param indep_var is a list of Variables
def model(dep_var: Variable, indep_vars: list, exper: Experiment):
    return Model(dep_var, indep_vars, exper)



# ## TODO: Min? Max? 
# univariate_stats = {'mean': UnivariateTest.mean, 
#                     'median': UnivariateTest.median,
#                     'standard deviation': UnivariateTest.std_dev,
#                     'variance': UnivariateTest.variance, 
#                     'kurtosis': UnivariateTest.kurtosis,
#                     'skew': UnivariateTest.skew,
#                     'normality': UnivariateTest.normality,
#                     'frequency': UnivariateTest.frequency}

# # Helper -- should make private? 
# def get_dataset(dataset_name: str) -> Dataset: 
#     if (dataset_name not in globals()): 
#         raise Exception('Dataset does not exist!') # Have some nicer error message
    
#     return globals()[dataset_name]


# # @returns a Dataset object? 
# def load_data(source: str, vars: Dict[str, Dict[str, list]] = None) -> Dataset: 
#     ds = Dataset()
#     ds.load_data(source)

#     for var_name in vars: 
#         v = vars[var_name]
#         data_type = None
#         categories = None
#         if (v['type'] == 'ordinal' or v['type'] == 'nominal'): 
#             # Create order tuple
#             categories = OrderedDict()
#             for i, c in enumerate(v['categories']):
#                 categories[c] = i+1
#         if (v['type'] == 'ordinal'): 
#             data_type = DataType.ORDINAL
#         elif (v['type'] == 'nominal'): 
#             data_type = DataType.NOMINAL
#         elif (v['type'] == 'interval'): 
#             data_type = DataType.INTERVAL
#         elif (v['type'] == 'ratio'): 
#             data_type = DataType.RATIO
#         else: 
#             raise Exception('Variables must be specified as being ordinal, nominal, interval, or ratio')
#         ds.set_variable(var_name, data_type, categories)
    
#     return ds

# def explore_summary(dataset: str, vars: Dict[str, Dict[str, list]]):
#         # TODO: do some error handling should the dictionary fields be mispelled, etc

#         result = list
#         data = get_dataset(dataset)
#         variable = data.get_variable(vars['variable'])
#         var = variable[0]
#         var_data = variable[1]
       
#         if 'characteristics' in vars: 
#             props = vars['characteristics']
#             if isinstance(props, str) and props.upper() == 'ALL': 
#                 props = list(univariate_stats.keys())
#         else: 
#             props = list(univariate_stats.keys())

#         for p in props: 
#             if (p not in univariate_stats.keys()):
#                 raise Exception(f"{p} is not a supported property of data")
            
#             statistic = univariate_stats[p]
#             result.append(p, evaluate(data, statistic(var), var, var_data))
#             # pretty_print(p, evaluate(data, var, statistic(var)))
        
#         pretty_print(result)
#         return result



# @attr.s(auto_attribs=True)
# class UnivariateTest(object): 
#     # dependent_variable: None # Do we need this??

#     def mean(var: Variable): 
#         # assert(var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO)

#         if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
#             return Mean(var)
#         elif (var.data_type == DataType.ORDINAL): 
#             return Mean_Ordinal(var)
#         else: 
#             raise Exception ('Cannot take mean of NOMINAL data!')

#     def median(var: Variable): 
#         if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
#             return Median(var)
#         elif (var.data_type == DataType.ORDINAL): 
#             return Median_Ordinal(var)
#         else: 
#             raise Exception ('Cannot take median of NOMINAL data!')
        

#     def std_dev(var: Variable): 
#         if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
#             return StandardDeviation(var)
#         elif (var.data_type == DataType.ORDINAL): 
#             return StandardDeviation_Ordinal(var)
#         else: 
#             raise Exception ('Cannot calculate standard deviation of NOMINAL data!')

#     def variance(var: Variable): 
#         if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
#             return Variance(var)
#         elif (var.data_type == DataType.ORDINAL): 
#             return Variance_Ordinal(var)
#         else: 
#             raise Exception ('Cannot calculate variance of NOMINAL data!')

#     def kurtosis(var: Variable): 
#         if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
#             return Kurtosis(var)
#         elif (var.data_type == DataType.ORDINAL): 
#             return Kurtosis_Ordinal(var)
#         else: 
#             raise Exception ('Cannot calculate kurtosis of NOMINAL data!') # TODO??????

#     def skew(var: Variable): 
#         if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
#             return Skew(var)
#         elif (var.data_type == DataType.ORDINAL): 
#             return Skew_Ordinal(var)
#         else: 
#             raise Exception ('Cannot calculate kurtosis of NOMINAL data!') # TODO??????
    
#     def normality(var: Variable): 
#         if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
#             return Normality(var)
#         elif (var.data_type == DataType.ORDINAL): 
#             return Normality_Ordinal(var)
#         else: 
#             raise Exception ('Cannot calculate normality (kurtosis, skew) of NOMINAL data!') # TODO??????

#     # Could be called on numeric and categorical data types
#     def frequency(var:Variable):
#         # May want to use Pandas (https://pandas.pydata.org/pandas-docs/stable/categorical.html#description)
#         if (var.data_type == DataType.INTERVAL or var.data_type == DataType.RATIO):
#             return Frequency(var)
#         else: # DataType.NOMINAL or DataType.ORDINAL
#             return Frequency_Categorical(var)

# def groups(dataset: Dataset, variable: Variable, sub_groups: Dict[str, Relation]=None): 

#     # if isinstance()
#     if (sub_groups): 
#         pass
#             # check_value_exists()
#             # calculate the values
#     else: 
#         pass
