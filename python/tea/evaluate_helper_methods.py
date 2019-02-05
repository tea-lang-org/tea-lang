from .ast import *
from .dataset import Dataset
from .evaluate_data_structures import VarData, CompData, ResData

import attr
from typing import Any
from types import SimpleNamespace # allows for dot notation access for dictionaries

from scipy import stats # Stats library used
import statsmodels.api as sm
import statsmodels.formula.api as smf
import numpy as np # Use some stats from numpy instead
import pandas as pd
import bootstrapped as bs

# Helper methods for Interpreter (in evaluate.py)
def compute_data_properties(dataset, expr: Node):
    if isinstance(expr, Compare):

        # Build up metadata for CompData to return
        # metadata = SimpleNamespace()
        # metadata.iv_name = expr.iv.name
        # metadata.iv_dtype = expr.iv.dtype
        # metadata.dv_name = expr.dv.name
        # metadata.dv_dtype = expr.dv.dtype

        # predictions = expr.predictions

        # Assumes we have categorical IV and continous DV
        # list of groups that we are interested in
        groups = []
        for p in expr.predictions:
            assert(p.lhs and p.rhs) # assert that each prediction has a lhs and rhs
            groups.append(p.lhs.value)
            groups.append(p.rhs.value)

        data = dict()
        #let's get data for those groups
        for g in groups: 
            where = expr.iv.name
            where += (" == \'" + g + "\'")
            data[g] = dataset.select(expr.dv.name, [where])
        # Try to create name that is unlikely for user to use
        # data['__NUM_GROUPS__'] = len(data) 
        # if iv is numeric, __NUM_GROUPS__ should be 1
        
        # import pdb; pdb.set_trace()
        # data = SimpleNamespace(**data)
        # import pdb; pdb.set_trace()

        # Calculate various stats/preconditional properties
        # Assign intermediate values to Simplenamespace var (see CompData vars)
        props = SimpleNamespace()
        # For debugging: Could change dist values here
        
        # distribution
        props.dist = compute_distribution(dataset.select(expr.dv.name))
        # variance
        props.var = compute_variance(data)

        # return CompData that has this data and other metadata
        return CompData(dataframes=data, properties=props)
        # return CompData(dataframes=data, metadata=metadata, predictions=predictions, properties=props)

def compute_distribution(data):
    # Check normality of data
    # https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.normaltest.html
    # Based on D’Agostino, R. B. (1971), “An omnibus test of normality for moderate and large sample size”, Biometrika, 58, 341-348
    # and D’Agostino, R. and Pearson, E. S. (1973), “Tests for departure from normality”, Biometrika, 60, 613-622
    # Null hypothesis is that distribution comes from Normal Distribution
    # Rejecting null means that distribution is NOT normal
    norm_test = stats.normaltest(data, axis=0)
    # return ('normality', norm_test[0], norm_test[1])
    return (norm_test[0], norm_test[1])

    # TODO: may want to compute/find the best distribution if not normal

def compute_variance(groups_data):
    # compute variance for each group

    # Levene test to test for equal variances - Leven is more robust to nonnormal data than Bartlett's test
    # Null Hypothesis is that samples have the same variances
    # Rejecting null means that samples have different variances
    # Default/currently using .05 alpha level
    # https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.levene.html#scipy.stats.levene
    
    keys = list(groups_data.keys())
    # levene_test = stats.levene({groups_data[k].values} for k in keys)
    
    levene_test = stats.levene(groups_data[keys[0]], groups_data[keys[1]])
    # return ('equal_variance', levene_test[0], levene_test[1])
    return (levene_test[0], levene_test[1])

"""
    return {
            'var_name': '',
            'ci_interval': '',
            'point_name': '',
            'point_est': '', 
            }
"""
    # raise Exception('Not implemented BOOTSTRAP')

def is_normal(data, alpha):
    norm_test = compute_distribution(data)
    return (norm_test[2] < .05)

def is_normal(comp_data: CompData, alpha):
    return comp_data.properties.dist[1] < alpha

# def is_equal_variance(iv_data: list):
#     # Check variance using Levene's test
#     eq_var = False
#     levene = stats.levene(iv_data[0], iv_data[1])
#     test_res = (levene.statistic, levene.pvalue)
#     if test_res[1] > .05: # cannot reject null hypothesis that two groups are from populations with equal variances
#         eq_var = True
    
#     return (eq_var, test_res)

def is_equal_variance(comp_data: CompData, alpha):
    return comp_data.properties.var[1] < alpha

def is_numeric(data_type: DataType):
    return data_type is DataType.INTERVAL or data_type is DataType.RATIO

def is_ordinal(data_type: DataType):
    return data_type is DataType.ORDINAL

def is_nominal(data_type: DataType):
    return data_type is DataType.NOMINAL

# TODO make more robust to variables that happen to be between/within -- random effects, not random effects, etc.
def is_independent_samples(var_name: str, design: Dict[str, str]):
    return var_name in design['between subjects'] if ('between subjects' in design) else False

def is_dependent_samples(var_name: str, design: Dict[str, str]):
    return var_name in design['within subjects'] if ('between subjects' in design) else False

# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.ttest_ind.html
# Possible parameters: a, b : array | axis (without, over entire arrays) | equal_var (default is True)
#                      nan_policy (optional) 
def t_test_ind(expr: Compare, comp_data: CompData, **kwargs):
    assert(len(comp_data.dataframes) == 2)
    assert(len(expr.predictions) == 1)

    data = []
    for key, val in comp_data.dataframes.items():
        data.append(val)

    # What if we just return a lambda and all the test signatures are the same? That way, easy to swap out with constraint version?
    return stats.ttest_ind(data[0], data[1], equal_var=is_equal_variance(comp_data, kwargs['alpha']))
    
    # import pdb; pdb.set_trace()

        # if (isinstance(pred, Equal) or isinstance(pred, NotEqual)):
    #             #     # two-tailed test
    #             #     raise NotImplemented
    #     pass
    # elif (isinstance(pred, LessThan) or isinstance(pred, LessThanEqual)): 
    #             #     # 1-tailed test
    #             #     # ??? How should treat the Les than EQUAL TO? 
    #             #     raise NotImplemented
    #     pass
    # elif (isinstance(pred, GreaterThan) or isinstance(pred, GreaterThanEqual)): 

    #                 corrected_pvalue = None
    #                 if (ttest.statistic > 0):
    #                     corrected_pvalue = ttest.pvalue * .5 
    #                 elif (ttest.statistic < 0): 
    #                     corrected_pvalue = 1 - (ttest.pvalue * .5)
    #                 else: 
    #                     raise ValueError(f"T statistic equals 0: {ttest.statistic}")
                    
    #                 return ResData(expr.iv, expr.dv, None, f"one-sided ttest with equal variance={eq_var}", [ttest.statistic, corrected_pvalue])

    # raise NotImplementedError

# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.mannwhitneyu.html
# Paramters: x, y : array_like | use_continuity (default=True, optional - for ties) | alternative (p-value for two-sided vs. one-sided)
def mann_whitney_u(expr: Compare, comp_data: CompData, **kwargs):
    assert(len(comp_data.dataframes) == 2)
    assert(len(expr.predictions) == 1)

    data = []
    for key, val in comp_data.dataframes.items():
        data.append(val)

    # What if we just return a lambda and all the test signatures are the same? That way, easy to swap out with constraint version?
    return stats.mannwhitneyu(data[0], data[1], alternative='two-sided')

# https://docs.scipy.org/doc/scipy-0.18.1/reference/generated/scipy.stats.fisher_exact.html#scipy.stats.fisher_exact
# Parmaters: table (2 x 2) | alternative (default='two-sided' optional)
def fishers_exact(expr: Compare, comp_data: CompData, **kwargs):
    assert(len(comp_data.dataframes) == 2)
    assert(len(expr.predictions) == 1)

    data = []
    # calculate the 2 x 2 table 
    table = []
    stats.fisher_exact(table, alternative='two-sided')

# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.ttest_rel.html
# Parameters: a, b (array-like) | axis | nan_policy (default is 'propagate', optional)
def t_test_paired(expr: Compare, comp_data: CompData, **kwargs):
    assert(len(comp_data.dataframes) == 2)
    assert(len(expr.predictions) == 1)

    data = []
    for key, val in comp_data.dataframes.items():
        data.append(val)

    return stats.ttest_rel(data[0], data[1])

# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.wilcoxon.html
# Parameters: x (array-like) | y (array-like, optional) | zero_method (default = 'wilcox', optional) | correction (continuity correction, optional)
def wilcoxon_signed_rank(expr: Compare, comp_data: CompData, **kwargs):
    assert(len(comp_data.dataframes) == 2)
    assert(len(expr.predictions) == 1)

    data = []
    for key, val in comp_data.dataframes.items():
        data.append(val)

    return stats.wilcoxon(data[0], data[1])

# https://docs.scipy.org/doc/scipy-0.14.0/reference/generated/scipy.stats.linregress.html
def linear_regression(expr: Compare, comp_data: CompData, **kwargs):

    return stats.linregress()
    

## NAIVE IMPLEMENTATION RIGHT NOW
# TODO: depending on ow linear constraing solver is implemented, may want to have two separate functions - 1) returns the name of the test/function and 2) get test with parameters, but not executed??
# Based on the properties of data, find the most appropriate test to conduct
# Return the test but do not execute
def find_test(dataset: Dataset, expr: Compare, comp_data: CompData, design: Dict[str, str], **kwargs):
    # Two IV groups (only applies to nominal/ordinal IVs)
    if (len(comp_data.dataframes) == 2):
        if (is_nominal(expr.iv.dtype) and is_independent_samples(expr.iv.name, design)):
            if (is_numeric(expr.dv.dtype) and is_normal(comp_data, kwargs['alpha'])):
                return lambda : t_test_ind(expr, comp_data, **kwargs)
            elif (is_numeric(expr.dv.dtype) or is_ordinal(expr.dv.data_type)):
                return lambda : mann_whitney_u(expr, comp_data, **kwargs)
            elif (is_nominal(expr.dv.dtype)):
                raise AssertionError('Not sure if Fishers is the correct test here - what if have more than 2 x 2 table??')
                return lambda : fishers_exact(expr, comp_data, **kwargs)
        elif (is_nominal(expr.iv.dtype) and is_dependent_samples(expr.iv.name, design)):
            if (is_numeric(expr.dv.dtype) and is_normal(comp_data, kwargs['alpha'])):
                return lambda : t_test_paired(expr, comp_data, **kwargs)
            elif (is_numeric(expr.dv.dtype) or is_ordinal(expr.dv.data_type)):
                return lambda : wilcoxon_signed_rank(expr, comp_data, **kwargs)
            elif (is_nominal(expr.dv.dtype)):
                raise AssertionError('Not sure if McNemar is the correct test here - what if have more than 2 x 2 table??')
                raise AssertionError('McNemar')
    elif (len(comp_data.dataframes) == 1 and is_numeric(expr.iv.dtype)): # OR MOVE TO/REPEAT in outer IF/ELSE for comp_data.dataframes == 1??
            if (is_numeric(expr.dv.dtype) and is_normal(comp_data, kwargs['alpha'])):
                # For Pearson, need to check that both IV and DV are normally distributed
                # if (is_normal(dataset[expr.iv.name], kwargs['alpha'])):
                #     # pearson
                # else: 
                #     # spearman
                
                #simple linear regression

                
                raise AssertionError('Not implemented - Correlation or Simple Linear Regression')
            elif (is_numeric(expr.dv.dtype) or is_ordinal(expr.dv.data_type)):
                raise AssertionError ('Not implemented - non-parametric correlation')
            elif (is_nominal(expr.dv.dtype)):
                raise AssertionError ('Not implemnted - simple logistic regression')
    elif (len(comp_data.dataframes) > 2):
        raise NotImplementedError
    else: 
        raise AssertionError('Trying to compare less than 1 variables....?')

                

# This is the function used to determine and then execute test based on CompData
def execute_test(dataset: Dataset, expr: Compare, data_props: CompData, design: Dict[str,str]): 
    # For power we need sample size, effect size, alpha
    sample_size = 0
    # calculate sample size
    for df in data_props.dataframes:
        sample_size += len(data_props.dataframes[df])

    effect_size = design['effect size'] if ('effect size' in design) else [.2, .5, .8] # default range unless user defines
    
    alpha = design['alpha'] if ('alpha' in design) else .05
    
    # Find test
    stat_test = find_test(dataset, expr, data_props, design, sample_size=sample_size, effect_size=effect_size, alpha=alpha)
    import pdb; pdb.set_trace()
    
    # Execute test
    results = stat_test()

    # Wrap results in ResData and return
    # Here we care about one-tailed vs. two-tailed
    # Could also account for multiple testing/correction here
    # HOW DO WE DEAL WITH MORE THAN ONE PREDICTION???
    # - should check that all predictions make sense (involve actual/legit values?)
    # - really a matter of INTREPRETATION for the predictions -- p-value, and maybe multiple comparison corrections??




    
    #  # If Nominal x Nominal, do X
    #     if (iv_dtype is DataType.NOMINAL):

    #         
    #     elif (iv_dtype is DataType.ORDINAL):

    #         central_tendencies = []
    #         for group in ivs: 
    #             # get the iv data for ivs
    #             data = dv.dataframe.loc(axis=0)[group.dataframe.index.values]

    #             # calculate some central tendency metric
    #             # Wilcoxon Mann Whitney U test
    #             import pdb; pdb.set_trace()
    #             metric = bootstrap(data) # how know which central tendency metric to calculate? -- based on data properties
            
    #         # compare these measures of central tendency
    #         # estimates (confidence intervals, etc)
    #         # ResData([{}, {}], test: '', test_results: '')
    #         # NHST tests?
            
            
    #         raise AssertionError('Not implemented - IV is ORDINAL -- may have some overlap with iv == NOMINAL')
    #     elif (iv_dtype is DataType.INTERVAL or iv_dtype is DataType.RATIO):
    #         raise AssertionError('Not implemented - IV is INTERVAL OR RATIO')
    #     else:
    #         raise ValueError('Should never get here. ')



    #     raise Exception('Not implemented Compare')
    
def bootstrap(data):
    import pdb; pdb.set_trace()
    print('Do something with incoming data')

