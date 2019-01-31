from .ast import *
from .dataset import Dataset

import attr
from typing import Any
from types import SimpleNamespace # allows for dot notation access for dictionaries

from scipy import stats # Stats library used
import statsmodels.api as sm
import statsmodels.formula.api as smf
import numpy as np # Use some stats from numpy instead
import pandas as pd
import bootstrapped as bs

# Eval : Dataset, Program (list of functions/stats) --> table of computed stats

# x = 1 
# -----
# y = 2
# -----
# z = x + y
# -------
# z = z + z
# ----------

# def f():
#     tree 

# f -> AST 


# class Evaluator(object):
#     def __init__(self, dataset, experiment_setup):
#         self.dataset = dataset.data #access to pd.DataFrame directly
#         self.experiment_setup = experiment_setup
#         self.stats = {}
    
#     def eval(self, model: Model):
#         self.stats = {}

#         dv = model.dependent_var
#         iv = model.eq_independent_vars
        
#         if (isinstance(iv, Variable)): # only one independent variable --> BIVARIATE ANALYSIS
#             if (iv.dtype == DataType.ORDINAL or iv.dtype == DataType.NOMINAL): 
#                 if (iv.etype == Experiment_DataType.BETWEEN_SUBJECTS): 
#                     if (dv.dtype == DataType.INTERVAL and isnormal(dv.data)): 
#                         # oneway interval ANOVA
#                         pass
#                     elif (dv.dtype == DataType.INTERVAL or dv.dtype == DataType.ORDINAL):
#                         # kruskal wallis 
#                         pass
#                     elif (dv.dtype == DataType.NOMINAL): 
#                         # chi square
#                         pass
#                     else: 
#                         raise ValueError(f"Do not support this yet: IV{iv.dtype}, {iv.etype} and DV{dv.dtype}, {dv.etype}")
#                 elif (iv.etype == Experiment_DataType.WITHIN_SUBJECTS):
#                     if (dv.dtype == DataType.INTERVAL and isnormal(dv.data)): 
#                         # one way repeated measures ANOVA
#                         pass
#                     elif (dv.dtype == DataType.INTERVAL or dv.dtype == DataType.ORDINAL): 
#                         # Friedman test
#                         pass
#                     elif (dv.dtype == DataType.NOMINAL):
#                         if (len(dv.categories) == 2): 
#                             # repeated measures logistic regression
#                             pass
#                         else: 
#                             print('What do we do here?')
#             else: # (iv.dtype == DataType.INTERVAL or iv.dtype == DataType.RATIO): 
#                 if (dv.dtype == DataType.INTERVAL and isnormal(dv.data)): 
#                     # correlation or simple linear regression
#                     pass
#                 elif (dv.dtype == DataType.INTERVAL or dv.dtype == DataType.ORDINAL): 
#                     # non-parametric correlation
#                     pass
#                 elif (dv.dtype == DataType.NOMINAL): 
#                     # simple logistic regression 
#                     pass
#                 else: 
#                     raise ValueError(f"Do not support this yet: IV{iv.dtype}, {iv.etype} and DV{dv.dtype}, {dv.etype}")

#         else: #multivariate analysis
#             # TODO: RATIO data? ORDINAL Data? 
#             if (dv.dtype == DataType.INTERVAL and isnormal(dv.data)):
#                 # multiple regression
#                 regression(self.dataset, model, self.stats)
#                 # ANCOVA 
#                 pass
#             elif (dv.dtype == DataType.NOMINAL): 
#                 # multiple logistic regression or discriminant analysis
#                 pass
#             else: 
#                 raise ValueError(f"Do not support this yet: IV{iv.dtype}, {iv.etype} and DV{dv.dtype}, {dv.etype}")


# def evaluate(dataset: Dataset, experiment_setup: Experiment_SetUp, model: Model, hypothesis: Hypothesis):
#     e = Evaluator(dataset, experiment_setup)
#     e.eval(model)
#     return e.stats


class Value(object):
    pass

@attr.s(init=True, auto_attribs=True)
class VarData(Value):
    dataframe: Any
    metadata: Any

@attr.s(init=True, auto_attribs=True)
class GroupsData(Value): # TODO probably want to rename this
    dataframes: Any
    metadata: Any  # not totally sure but could include vardata types? 
    # list of characteristics about the groups that are used to determine statistical test
    distribution: Any 
    variance: Any 


@attr.s(init=True, auto_attribs=True, str=False)
class ResData(Value):
    # groups: Any # What groups were compared?
    # ci_intervals: Any # CI intervals for each group
    # point_estimates: Any # point estimate for each group
    # # interpretation: Any ????
    
    ivs: Any # Results from central tendency procedure for groups compared??
    dv: Any
    group_results: Any # Results from central tendency procedure for groups compared??
    test: Any # name? of test conducted to compare groups (whose results are stored in group_results)
    test_results: Any # result of conducting above test

    def __str__(self):
        summary = f"Compared {self.dv} as dependent variables between independent variables: {self.ivs}"
        test = f"\nConducted {self.test}: test statistic: {self.test_results[0]}, p-value: {self.test_results[1]}"

        return summary + test

def evaluate(dataset: Dataset, expr: Node, design: Dict[str, Value]=None):
    if isinstance(expr, Variable):
        dataframe = dataset[expr.name]
        metadata = dataset.get_variable_data(expr.name) # (dtype, categories)
        return VarData(dataframe, metadata)

    elif isinstance(expr, Literal):
        data = pd.Series([expr.value] * len(dataset.data), index=dataset.data.index) # Series filled with literal value
        metadata = None # metadata=None means literal
        return VarData(data, metadata)

    elif isinstance(expr, Equal):
        lhs = evaluate(dataset, expr.lhs)
        rhs = evaluate(dataset, expr.rhs)
        assert isinstance(lhs, VarData)
        assert isinstance(rhs, VarData)
        
        dataframe = lhs.dataframe[lhs.dataframe == rhs.dataframe]
        metadata = lhs.metadata
        return VarData(dataframe, metadata)

    elif isinstance(expr, NotEqual): 
        rhs = evaluate(dataset, expr.rhs)
        lhs = evaluate(dataset, expr.lhs)
        assert isinstance(rhs, VarData)
        assert isinstance(lhs, VarData)
        
        dataframe = lhs.dataframe[lhs.dataframe != rhs.dataframe]
        metadata = lhs.metadata
        return VarData(dataframe, metadata)

    elif isinstance(expr, LessThan):
        lhs = evaluate(dataset, expr.lhs)
        rhs = evaluate(dataset, expr.rhs)
        assert isinstance(lhs, VarData)
        assert isinstance(rhs, VarData)


        dataframe = None
        metadata = rhs.metadata
        
        if (not lhs.metadata):
            raise ValueError('Malformed Relation. Filter on Variables must have variable as rhs')
        elif (lhs.metadata['dtype'] is DataType.NOMINAL):
            raise ValueError('Cannot compare nominal values with Less Than')
        elif (lhs.metadata['dtype'] is DataType.ORDINAL):
            assert (rhs.metadata is None) # May want to add a case should RHS and LHS both be variables
            comparison = rhs.dataframe.iloc[0]
            if (isinstance(comparison, str)):
                categories = lhs.metadata['categories'] # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids  = [i for i,x in enumerate(lhs.dataframe) if categories[x] < categories[comparison]]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name
                
            elif (np.issubdtype(comparison, np.integer)):
                categories = lhs.metadata['categories'] # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids  = [i for i,x in enumerate(lhs.dataframe) if categories[x] < comparison]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name                

            else: 
                raise ValueError(f"Cannot compare ORDINAL variables to {type(rhs.dataframe.iloc[0])}")


        elif (lhs.metadata['dtype'] is DataType.INTERVAL or lhs.metadata['dtype'] is DataType.RATIO):
            comparison = rhs.dataframe.iloc[0]
             # Get raw Pandas Series indices for desired data
            ids  = [i for i,x in enumerate(lhs.dataframe) if x < comparison]
            # Get Pandas Series set indices for desired data
            p_ids = [lhs.dataframe.index.values[i] for i in ids]
            # Create new Pandas Series with only the desired data, using set indices
            dataframe = pd.Series(lhs.dataframe, p_ids)
            dataframe.index.name = dataset.pid_col_name   

        else:
            raise Exception(f"Invalid Less Than Operation:{lhs} < {rhs}")

        
        return VarData(dataframe, metadata)

    elif isinstance(expr, LessThanEqual):
        lhs = evaluate(dataset, expr.lhs)
        rhs = evaluate(dataset, expr.rhs)
        assert isinstance(lhs, VarData)
        assert isinstance(rhs, VarData)


        dataframe = None
        metadata = rhs.metadata
        
        if (not lhs.metadata):
            raise ValueError('Malformed Relation. Filter on Variables must have variable as rhs')
        elif (lhs.metadata['dtype'] is DataType.NOMINAL):
            raise ValueError('Cannot compare nominal values with Less Than')
        elif (lhs.metadata['dtype'] is DataType.ORDINAL):
            assert (rhs.metadata is None) # May want to add a case should RHS and LHS both be variables
            comparison = rhs.dataframe.iloc[0]
            if (isinstance(comparison, str)):
                categories = lhs.metadata['categories'] # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids  = [i for i,x in enumerate(lhs.dataframe) if categories[x] <= categories[comparison]]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name
                
            elif (np.issubdtype(comparison, np.integer)):
                categories = lhs.metadata['categories'] # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids  = [i for i,x in enumerate(lhs.dataframe) if categories[x] <= comparison]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name                

            else: 
                raise ValueError(f"Cannot compare ORDINAL variables to {type(rhs.dataframe.iloc[0])}")


        elif (lhs.metadata['dtype'] is DataType.INTERVAL or lhs.metadata['dtype'] is DataType.RATIO):
            comparison = rhs.dataframe.iloc[0]
             # Get raw Pandas Series indices for desired data
            ids  = [i for i,x in enumerate(lhs.dataframe) if x <= comparison]
            # Get Pandas Series set indices for desired data
            p_ids = [lhs.dataframe.index.values[i] for i in ids]
            # Create new Pandas Series with only the desired data, using set indices
            dataframe = pd.Series(lhs.dataframe, p_ids)
            dataframe.index.name = dataset.pid_col_name   

        else:
            raise Exception(f"Invalid Less Than Equal Operation:{lhs} <= {rhs}")


        return VarData(dataframe, metadata)
    
    elif isinstance(expr, GreaterThan):
        lhs = evaluate(dataset, expr.lhs)
        rhs = evaluate(dataset, expr.rhs)
        assert isinstance(lhs, VarData)
        assert isinstance(rhs, VarData)


        dataframe = None
        metadata = rhs.metadata
        
        if (not lhs.metadata):
            raise ValueError('Malformed Relation. Filter on Variables must have variable as rhs')
        elif (lhs.metadata['dtype'] is DataType.NOMINAL):
            raise ValueError('Cannot compare nominal values with Greater Than')
        elif (lhs.metadata['dtype'] is DataType.ORDINAL):
            assert (rhs.metadata is None) # May want to add a case should RHS and LHS both be variables
            comparison = rhs.dataframe.iloc[0]
            if (isinstance(comparison, str)):
                categories = lhs.metadata['categories'] # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids  = [i for i,x in enumerate(lhs.dataframe) if categories[x] > categories[comparison]]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name
                
            elif (np.issubdtype(comparison, np.integer)):
                categories = lhs.metadata['categories'] # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids  = [i for i,x in enumerate(lhs.dataframe) if categories[x] > comparison]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name                

            else: 
                raise ValueError(f"Cannot compare ORDINAL variables to {type(rhs.dataframe.iloc[0])}")


        elif (lhs.metadata['dtype'] is DataType.INTERVAL or lhs.metadata['dtype'] is DataType.RATIO):
            comparison = rhs.dataframe.iloc[0]
             # Get raw Pandas Series indices for desired data
            ids  = [i for i,x in enumerate(lhs.dataframe) if x > comparison]
            # Get Pandas Series set indices for desired data
            p_ids = [lhs.dataframe.index.values[i] for i in ids]
            # Create new Pandas Series with only the desired data, using set indices
            dataframe = pd.Series(lhs.dataframe, p_ids)
            dataframe.index.name = dataset.pid_col_name   

        else:
            raise Exception(f"Invalid Greater Than Operation:{lhs} > {rhs}")

        return VarData(dataframe, metadata) 
   
    elif isinstance(expr, GreaterThanEqual):
        lhs = evaluate(dataset, expr.lhs)
        rhs = evaluate(dataset, expr.rhs)
        assert isinstance(lhs, VarData)
        assert isinstance(rhs, VarData)


        dataframe = None
        metadata = rhs.metadata
        
        if (not lhs.metadata):
            raise ValueError('Malformed Relation. Filter on Variables must have variable as rhs')
        elif (lhs.metadata['dtype'] is DataType.NOMINAL):
            raise ValueError('Cannot compare nominal values with Greater Than Equal')
        elif (lhs.metadata['dtype'] is DataType.ORDINAL):
            assert (rhs.metadata is None) # May want to add a case should RHS and LHS both be variables
            comparison = rhs.dataframe.iloc[0]
            if (isinstance(comparison, str)):
                categories = lhs.metadata['categories'] # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids  = [i for i,x in enumerate(lhs.dataframe) if categories[x] >= categories[comparison]]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name
                
            elif (np.issubdtype(comparison, np.integer)):
                categories = lhs.metadata['categories'] # OrderedDict
                # Get raw Pandas Series indices for desired data
                ids  = [i for i,x in enumerate(lhs.dataframe) if categories[x] >= comparison]
                # Get Pandas Series set indices for desired data
                p_ids = [lhs.dataframe.index.values[i] for i in ids]
                # Create new Pandas Series with only the desired data, using set indices
                dataframe = pd.Series(lhs.dataframe, p_ids)
                dataframe.index.name = dataset.pid_col_name                

            else: 
                raise ValueError(f"Cannot compare ORDINAL variables to {type(rhs.dataframe.iloc[0])}")


        elif (lhs.metadata['dtype'] is DataType.INTERVAL or lhs.metadata['dtype'] is DataType.RATIO):
            comparison = rhs.dataframe.iloc[0]
             # Get raw Pandas Series indices for desired data
            ids  = [i for i,x in enumerate(lhs.dataframe) if x >= comparison]
            # Get Pandas Series set indices for desired data
            p_ids = [lhs.dataframe.index.values[i] for i in ids]
            # Create new Pandas Series with only the desired data, using set indices
            dataframe = pd.Series(lhs.dataframe, p_ids)
            dataframe.index.name = dataset.pid_col_name   

        else:
            raise Exception(f"Invalid Greater Than Equal Operation:{lhs} >= {rhs}")

        return VarData(dataframe, metadata) 

    # elif isinstance(expr, Relate): 
    #     raise Exception('Not implemented RELATE')

    elif isinstance(expr, Compare): 
        ivs = is_well_formed_compare(dataset, expr)

        # Form dictionary with characteristics that we care about
        # {
        #     # These could be Power data structure or passed separately from the Groups data
        #     'sample size': , # could be range (instead of single val)
        #     'effect size': , # could be range (instead of single val)
        #     'alpha': , # Type 1 error rate

        #     # in GroupsData 
        #     'normality': normality_test, # could also be more generic distribution info
        #     'equal_variance': equal_variance,
        #     'correlation': 
        #     #'' other things!
        # }

        iv_dtype = ivs[0].metadata['dtype']
        dv = evaluate(dataset, expr.dv)
        assert isinstance(dv, VarData)

        # Check properties of the data
        #TODO: Computed Properties of Data
        #[dtypes, normality test, residuals?, variance]


        iv_data = [] # 2D array corresponding to data from each group, group[i]'s data is in iv_data[i]
        for g in ivs: 
            ind = g.dataframe.index.values
            import pdb; pdb.set_trace()
            group_data = [dv.dataframe.loc[i] for i in ind]
            iv_data.append(group_data)
        
        # Check variance using Levene's test
        eq_var = False
        levene = stats.levene(iv_data[0], iv_data[1]).pvalue
        if levene > .05: # cannot reject null hypothesis that two groups are from populations with equal variances
            eq_var = True
        


        # If Nominal x Nominal, do X
        if (iv_dtype is DataType.NOMINAL):
            if ((dv.metadata['dtype'] is DataType.INTERVAL or dv.metadata['dtype'] is DataType.RATIO) and isnormal(dv.dataframe)):
                # 2-tailed vs. 1 -tailed -- based on hypothesis

                if (isinstance(expr.prediction, Equal) or isinstance(expr.prediction, NotEqual)):
                    # two-tailed test
                    raise NotImplemented
                elif (isinstance(expr.prediction, LessThan) or isinstance(expr.prediction, LessThanEqual)): 
                    # 1-tailed test
                    # ??? How should treat the Les than EQUAL TO? 
                    raise NotImplemented
                elif (isinstance(expr.prediction, GreaterThan) or isinstance(expr.prediction, GreaterThanEqual)): 
                    # 1-tailed test
                    # ??? How should treat the Les than EQUAL TO?
                    
                    if (expr.iv.name in design['between subjects']):
                        # independent samples
                        ttest = stats.ttest_ind(iv_data[0], iv_data[1], equal_var=eq_var)
                    elif (expr.iv.name in design['within subjects']):
                        # dependent samples
                        
                        # split the samples
                        import pdb; pdb.set_trace()
                        ttest = stats.ttest_ind(iv_data[0], iv_data[1], equal_var=eq_var)

                    corrected_pvalue = None
                    if (ttest.statistic > 0):
                        corrected_pvalue = ttest.pvalue * .5 
                    elif (ttest.statistic < 0): 
                        corrected_pvalue = 1 - (ttest.pvalue * .5)
                    else: 
                        raise ValueError(f"T statistic equals 0: {ttest.statistic}")
                    
                    return ResData(expr.iv, expr.dv, None, f"one-sided ttest with equal variance={eq_var}", [ttest.statistic, corrected_pvalue])

                

            elif (dv.metadata['dtype'] is DataType.ORDINAL or iv_dtype is DataType.INTERVAL or dv.metadata['dtype'] is DataType.RATIO):
                raise AssertionError ('Not implemented - Wilcoxon, Mann Whitney test')
            
            elif (dv.metadata['dtype'] is DataType.NOMINAL):
                raise AssertionError ('Not implemnted - Chi square or Fishers Exact Test')
        elif (iv_dtype is DataType.ORDINAL):

            central_tendencies = []
            for group in ivs: 
                # get the iv data for ivs
                data = dv.dataframe.loc(axis=0)[group.dataframe.index.values]

                # calculate some central tendency metric
                # Wilcoxon Mann Whitney U test
                import pdb; pdb.set_trace()
                metric = bootstrap(data) # how know which central tendency metric to calculate? -- based on data properties
            
            # compare these measures of central tendency
            # estimates (confidence intervals, etc)
            # ResData([{}, {}], test: '', test_results: '')
            # NHST tests?
            
            
            raise AssertionError('Not implemented - IV is ORDINAL -- may have some overlap with iv == NOMINAL')
        elif (iv_dtype is DataType.INTERVAL or iv_dtype is DataType.RATIO):
            raise AssertionError('Not implemented - IV is INTERVAL OR RATIO')
        else:
            raise ValueError('Should never get here. ')



        raise Exception('Not implemented Compare')
    
    elif isinstance(expr, Mean):
        var = evaluate(dataset, expr.var)
        assert isinstance(var, VarData)

        bs.bootstrap(var.dataframe, stat_func=bs_stats.mean)
        raise Exception('Not implemented Mean')
    
    # elif isinstance(expr, Median):
    #     raise Exception('Not implemented Median')


    
    # elif isinstance(expr, Add): 
    #     raise Exception('Not implemented Add')

    # TODO all the other arithmetic....

# def isnormal(data): 
#     return 

# helper method
def bootstrap(data):
    import pdb; pdb.set_trace()
    print('Do something with incoming data')


# @returns array of variables 
def is_well_formed_compare(dataset, expr):
    xs = [] # list of variables comparing

    # Check "well-formedness"
    for e in expr.groups: 
        group = evaluate(dataset, e)
        assert isinstance(group, VarData)
        xs.append(group)
    assert (len(xs) == 2) # Just comparing 2 groups for now
    assert (xs[0].metadata['dtype'] == xs[1].metadata['dtype']) # assert they are the same datatype

    return xs

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
    return True

# TODO More USER FACING
# Takes all evaluated results, stores for call and then outputs the results in a dictionary/table
# def eval(dataset, args*):
#     results = {}
#     for e in args*: 
#         results[e] = evaluate(dataset, expr)
    
#     return eval 