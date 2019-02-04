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
        
        # import pdb; pdb.set_trace()
        # data = SimpleNamespace(**data)
        # import pdb; pdb.set_trace()

        # Calculate various stats/preconditional properties
        # Assign intermediate values to simplenamespace var (see CompData vars)
        props = SimpleNamespace()
        # For debugging: Could change dist values here
        
        # distribution
        props.dist = compute_distribution(dataset.select(expr.dv.name))
        # variance
        props.var = compute_variance(data)

        # What is the metadata for CompData?

        # return CompData that has this data and other metadata
        return CompData(data, props)

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

def is_normal(data):
    norm_test = compute_distribution(data)
    return (norm_test[2] < .05)

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

def isnormal(data): 
    normality = stats.normaltest(data)

def is_equal_variance(iv_data: list):
    # Check variance using Levene's test
    eq_var = False
    levene = stats.levene(iv_data[0], iv_data[1])
    test_res = (levene.w, levene.pvalue)
    if test_res[1] > .05: # cannot reject null hypothesis that two groups are from populations with equal variances
        eq_var = True
    
    return (eq_var, test_res)

def execute_test(dataset: Dataset, data_props: CompData, design: Dict[str,str]): 
    raise NotImplemented
    
    #  # If Nominal x Nominal, do X
    #     if (iv_dtype is DataType.NOMINAL):
    #         if ((dv.metadata['dtype'] is DataType.INTERVAL or dv.metadata['dtype'] is DataType.RATIO) and isnormal(dv.dataframe)):
    #             # 2-tailed vs. 1 -tailed -- based on hypothesis

    #             if (isinstance(expr.prediction, Equal) or isinstance(expr.prediction, NotEqual)):
    #                 # two-tailed test
    #                 raise NotImplemented
    #             elif (isinstance(expr.prediction, LessThan) or isinstance(expr.prediction, LessThanEqual)): 
    #                 # 1-tailed test
    #                 # ??? How should treat the Les than EQUAL TO? 
    #                 raise NotImplemented
    #             elif (isinstance(expr.prediction, GreaterThan) or isinstance(expr.prediction, GreaterThanEqual)): 
    #                 # 1-tailed test
    #                 # ??? How should treat the Les than EQUAL TO?
                    
    #                 if (expr.iv.name in design['between subjects']):
    #                     # independent samples
    #                     ttest = stats.ttest_ind(iv_data[0], iv_data[1], equal_var=eq_var)
    #                 elif (expr.iv.name in design['within subjects']):
    #                     # dependent samples
                        
    #                     # split the samples
    #                     import pdb; pdb.set_trace()
    #                     ttest = stats.ttest_ind(iv_data[0], iv_data[1], equal_var=eq_var)

    #                 corrected_pvalue = None
    #                 if (ttest.statistic > 0):
    #                     corrected_pvalue = ttest.pvalue * .5 
    #                 elif (ttest.statistic < 0): 
    #                     corrected_pvalue = 1 - (ttest.pvalue * .5)
    #                 else: 
    #                     raise ValueError(f"T statistic equals 0: {ttest.statistic}")
                    
    #                 return ResData(expr.iv, expr.dv, None, f"one-sided ttest with equal variance={eq_var}", [ttest.statistic, corrected_pvalue])

                

    #         elif (dv.metadata['dtype'] is DataType.ORDINAL or iv_dtype is DataType.INTERVAL or dv.metadata['dtype'] is DataType.RATIO):
    #             raise AssertionError ('Not implemented - Wilcoxon, Mann Whitney test')
            
    #         elif (dv.metadata['dtype'] is DataType.NOMINAL):
    #             raise AssertionError ('Not implemnted - Chi square or Fishers Exact Test')
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

