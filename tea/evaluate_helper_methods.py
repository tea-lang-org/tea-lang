from .ast import *
from .dataset import Dataset
from .evaluate_data_structures import VarData, CombinedData, BivariateData, MultivariateData, ResData

import attr
from typing import Any
from types import SimpleNamespace # allows for dot notation access for dictionaries
import copy

from scipy import stats # Stats library used
import statsmodels.api as sm
import statsmodels.formula.api as smf
# import numpy as np # Use some stats from numpy instead
import pandas as pd
import bootstrapped as bs

study_type_identifier = 'study type'
experiment_identifier = 'experiment'
observational_identifier = 'observational study'
iv_identifier = 'independent variables'
dv_identifier = 'dependent variables'
null_identifier = 'variables'
outcome_identifier = 'outcome variables'
contributor_identifier = 'contributor variables'
#quasi_experiment = 'quasi_experiment'

name = 'var_name'
data_type = 'dtype'
categories = 'categories'

# GLOBAL Property names
distribution = 'distribution'
variance = 'variance'
sample_size = 'sample size'
num_categories = 'number of categories'
eq_variance = 'equal variance'

def determine_study_type(vars_data: list, design: Dict[str, str]):
    if design: 
        # Is the study type explicit? If so...
        if (study_type_identifier in design):
            # Is this study an experiment?
            if (design[study_type_identifier] == experiment_identifier):
                return experiment_identifier
            # Is this study an observational study?
            elif (design[study_type_identifier] == observational_identifier):
                return observational_identifier
            # We don't know what kind of study this is.
            else: 
                raise ValueError(f"Type of study is not supported:{design[study_type_identifier]}. Is it an experiment or an observational study?")
        # The study type is not explicit, so let's check the other properties...
        else: 
            # This might be an experiment.
            if (iv_identifier in design and dv_identifier in design): # dv_identifier??
                return experiment_identifier
            elif (contributor_identifier in design and outcome_identifier in design):
                return observational_identifier
            # We don't know what kind of study this is.
            else: 
                raise ValueError(f"Type of study is not supported:{design}. Is it an experiment or an observational study?") 
        


# @returns list of VarData objects with same info as @param vars but with one updated role characteristic
def assign_roles(vars_data: list, study_type: str, design: Dict[str, str]):
    vars = copy.deepcopy(vars_data)

    if study_type == experiment_identifier:
        ivs = design[iv_identifier] if isinstance(design[iv_identifier], list) else [design[iv_identifier]]
        dvs = design[dv_identifier] if isinstance(design[dv_identifier], list) else [design[dv_identifier]]

        for v in vars:
            if v.metadata[name] in ivs:
                setattr(v, 'role', iv_identifier)
            elif v.metadata[name] in dvs: 
                setattr(v, 'role', dv_identifier)
            else: 
                setattr(v, 'role', null_identifier) ## may need to be the covariates
    elif study_type == observational_identifier:
        contributors = design[contributor_identifier] if isinstance(design[contributor_identifier], list) else [design[contributor_identifier]]
        outcomes = design[outcome_identifier] if isinstance(design[outcome_identifier], list) else [design[outcome_identifier]]

        for v in vars: 
            if v.metadata[name] in contributors:
                setattr(v, 'role', contributor_identifier)
            elif v.metadata[name] in outcomes: 
                setattr(v, 'role', outcome_identifier)
            else: 
                setattr(v, 'role', null_identifier) ## may need to change

            # We don't know what kind of study this is.
    else: 
        raise ValueError(f"Type of study is not supported:{design[study_type_identifier]}. Is it an experiment or an observational study?")
    
    return vars

# BOOTSTRAPPING!! 

# Helper methods for Interpreter (in evaluate.py)
# Compute properties about the VarData objects in @param vars using data in @param dataset
def compute_data_properties(dataset, vars_data: list):
    vars = copy.deepcopy(vars_data)

    for v in vars_data:
        v.properties[sample_size] = len(dataset.select(v.metadata[name]))
        if v.is_continuous(): 
            v.properties[distribution] = compute_distribution(dataset.select(v.metadata[name]))
            v.properties[variance] = compute_variance(dataset.select(v.metadata[name]))
        elif v.is_categorical(): 
            v.properties[num_categories] = len(v.metadata[categories])
        else: 
            raise ValueError (f"Not supported data type: {v.metadata[data_type]}")

    return vars

# Add equal variance property to @param combined_data
def add_eq_variance_property(dataset, combined_data: CombinedData, study_type: str): 
    vars = combined_data.vars
    xs = None
    ys = None
    cat_xs = []
    cont_ys = []
    grouped_data = []

    if study_type == experiment_identifier: 
        # Just need one variable to be Catogrical and another to be Continuous (regardless of role) -- both could be variable_identifier types
        xs = combined_data.get_vars(iv_identifier) 
        ys = combined_data.get_vars(dv_identifier) 
        
    else: # study_type == observational_identifier
        xs = combined_data.get_vars(contributor_identifier)
        ys = combined_data.get_vars(outcome_identifier)
    
    for x in xs: 
        if x.is_categorical(): 
            cat_xs.append(x)
    
    for y in ys: 
        if y.is_continuous(): 
            cont_ys.append(y)
    
    if cat_xs and cont_ys: 
        for y in ys:
            for x in xs: 
                cat = [k for k,v in x.metadata[categories].items()]
                for c in cat: 
                    data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
                    grouped_data.append(data)
                if isinstance(combined_data, BivariateData):
                    eq_var = compute_eq_variance(grouped_data)
                    import pdb; pdb.set_trace()
                    combined_data.properties[eq_variance] = eq_var
                elif isinstance(combined_data, MultivariateData):
                    combined_data.properties[eq_variance + '::' + x.metadata[name] + ':' + y.metadata[name]] = compute_eq_variance(grouped_data)
                else: 
                    raise ValueError(f"combined_data_data object is neither BivariateData nor MultivariateData: {type(combined_data)}")
    else: 
        combined_data.properties[eq_variance] = None
    

# Compute properties that are between/among VarData objects
def compute_combined_data_properties(dataset, combined_data: CombinedData, study_type: str, design: Dict[str, str]=None):
    assert (study_type == experiment_identifier or study_type == observational_identifier)
    combined = copy.deepcopy(combined_data)

    import pdb; pdb.set_trace()
    add_eq_variance_property(dataset, combined, study_type)
    
    import pdb; pdb.set_trace()

    

            
    
    # combined has a categorical iv --> then select data for each group from dataset 
    # -- dv/other variable can be continuous (maybe not nominal)
    #  
    # calculate leven test and assign to eq_variance


    # cacluclate distribvution here (differnt from indivdiual variable distribution info)
    ## TODO: Does it make sense to calculate equal variance when this is not the case???

    # for v in vars: 
        # import pdb; pdb.set_trace()
        
        # combined.properties[eq_variance] = compute_eq_variance(dataset.select())



    return combined

# @param vars is a list of VarData containing VarData objects of the variables we are interested in relating/analyzing
def compute_data_properties_og(dataset, vars: list, predictions: list=None, design: Dict[str, str]=None):
    global experiment_identifier, observational_identifier

    # Is this an experiment?
    if (design and (study_type_identifier in design.keys()) and (experiment_identifier == design[study_type_identifier])):

        ivs = [v for v in vars if v.metadata['var_name'] in design[iv_identifier]]
        dvs = [v for v in vars if v.metadata['var_name'] in design[dv_identifier]]
        covariates = [v for v in vars if v not in ivs and v not in dvs]
        
        if (len(covariates) > 0):
            # TODO Ask the user if they really want to do this analysis?
            pass
        
        ## WHAT IF WANT TO COMPARE COVARIATES?, COVARIATE + IV, COVARIATE + DV, DV + DV, IV + IV, etc???

        
        comp_data = []
        for dv in dvs: 
            data = dict() # Store data for which we want to compute properties
            for iv in ivs: 
                if (is_nominal(iv.metadata['dtype']) or is_ordinal(iv.metadata['dtype'])):
                    # list of groups that we are interested in
                    groups = []
                    for p in predictions:
                        assert(p.lhs and p.rhs) # assert that each prediction has a lhs and rhs
                        groups.append(p.lhs.value)
                        groups.append(p.rhs.value)
                    
                    #Let's get data for those groups
                    for g in groups: 
                        assert(not iv.metadata['query'] and not dv.metadata['query'])
                        where = iv.metadata['var_name']
                        where += (" == \'" + g + "\'")
                        data[g] = dataset.select(dv.metadata['var_name'], [where])

                elif (is_numeric(iv.metadata['dtype'])):
                    import pdb; pdb.set_trace()
                    
                    # Get data from dataset
                    data[iv.metadata['var_name']] = dataset.select(iv.metadata['var_name']) # add where clause as second parameter to dataset.select ??
                    data[dv.metadata['var_name']] = dataset.select(dv.metadata['var_name'])
                else: 
                    raise ValueError(f"Invalid variable type for IV: {iv.metadata['dtype']}")

            # Calculate various stats/preconditional properties for the data we are interested in
            # for d in data: ....
            props = dict()
            # For debugging: Could change dist values here

            if (is_numeric(dv.metadata['dtype'])):
                # distribution
                props[distribution] = compute_distribution(dataset.select(dv.metadata['var_name']))
                # variance
                import pdb; pdb.set_trace()
                props[variance] = compute_variance(data)
            elif (is_nominal(dv.metadata['dtype'])):
                raise NotImplementedError
            elif (is_ordinal(dv.metadata['dtype'])):
                raise NotImplementedError
                # could do something with the values (the numeric value of the ordinal keys)
            else:
                raise ValueError(f"Invalid dependent variable variable type: {dv.metadata['dtype']}")

            # return CombinedData that has this data and other metadata
            comp_data.append(CombinedData(dataframes=data, properties=props))
    # We are looking at an observational study
    else:
        raise NotImplementedError

    return comp_data

# Check normality of data
# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.normaltest.html
# Based on D’Agostino, R. B. (1971), “An omnibus test of normality for moderate and large sample size”, Biometrika, 58, 341-348
# and D’Agostino, R. and Pearson, E. S. (1973), “Tests for departure from normality”, Biometrika, 60, 613-622
# Null hypothesis is that distribution comes from Normal Distribution
# Rejecting null means that distribution is NOT normal
def compute_distribution(data):
    norm_test = stats.normaltest(data, axis=0)
    # could just reutrn norm_test directly???
    return (norm_test[0], norm_test[1])
    # TODO: may want to compute/find the best distribution if not normal
 
# @returns bootstrapped variance for @param data
def compute_variance(data): 
    return -1

# Levene test to test for equal variances - Leven is more robust to nonnormal data than Bartlett's test
# Null Hypothesis is that samples have the same variances
# Rejecting null means that samples have different variances
# Default/currently using .05 alpha level
# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.levene.html#scipy.stats.levene

def compute_eq_variance(groups_data):
    levene_test = stats.levene(*groups_data)
    return (levene_test[0], levene_test[1])

def is_normal(comp_data: CombinedData, alpha, data=None):
    if (data is not None): # raw data being checked for normality
        norm_test = compute_distribution(data)
        return (norm_test[1] < .05)
    else: 
        return comp_data.properties.dist[1] < alpha

def is_equal_variance(comp_data: CombinedData, alpha):
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
# Possible parameters: a, b : array | axis (without, over entire arrays) | equal_var (default is True) | nan_policy (optional) 
def t_test_ind(iv: VarData, dv: VarData, predictions: list, comp_data: CombinedData, **kwargs):
    assert(len(comp_data.dataframes) == 2)
    assert(len(predictions) == 1)

    data = []
    for key, val in comp_data.dataframes.items():
        data.append(val)

    # What if we just return a lambda and all the test signatures are the same? That way, easy to swap out with constraint version?
    return stats.ttest_ind(data[0], data[1], equal_var=is_equal_variance(comp_data, kwargs['alpha']))

# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.mannwhitneyu.html
# Paramters: x, y : array_like | use_continuity (default=True, optional - for ties) | alternative (p-value for two-sided vs. one-sided)
def mann_whitney_u(iv: VarData, dv: VarData, predictions: list, comp_data: CombinedData, **kwargs):
    assert(len(comp_data.dataframes) == 2)
    assert(len(predictions) == 1)

    data = []
    for key, val in comp_data.dataframes.items():
        # Use numbers for categories in ordinal data
        if (is_ordinal(dv.metadata['dtype'])):
            numeric = [dv.metadata['categories'][x] for x in val]
            val = numeric

        data.append(val)

    # What if we just return a lambda and all the test signatures are the same? That way, easy to swap out with constraint version?
    return stats.mannwhitneyu(data[0], data[1], alternative='two-sided')

# https://docs.scipy.org/doc/scipy-0.18.1/reference/generated/scipy.stats.fisher_exact.html#scipy.stats.fisher_exact
# Parmaters: table (2 x 2) | alternative (default='two-sided' optional)
def fishers_exact(iv: VarData, dv: VarData, predictions: list, comp_data: CombinedData, **kwargs):
    assert(len(comp_data.dataframes) == 2)
    assert(len(predictions) == 1)

    data = []
    # calculate the 2 x 2 table 
    table = []
    stats.fisher_exact(table, alternative='two-sided')

# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.ttest_rel.html
# Parameters: a, b (array-like) | axis | nan_policy (default is 'propagate', optional)
def t_test_paired(iv: VarData, dv: VarData, predictions: list, comp_data: CombinedData, **kwargs):
    assert(len(comp_data.dataframes) == 2)
    assert(len(predictions) == 1)

    data = []
    for key, val in comp_data.dataframes.items():
        data.append(val)

    return stats.ttest_rel(data[0], data[1])

# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.wilcoxon.html
# Parameters: x (array-like) | y (array-like, optional) | zero_method (default = 'wilcox', optional) | correction (continuity correction, optional)
def wilcoxon_signed_rank(iv: VarData, dv: VarData, predictions: list, comp_data: CombinedData, **kwargs):
    assert(len(comp_data.dataframes) == 2)
    assert(len(predictions) == 1)

    data = []
    for key, val in comp_data.dataframes.items():
        # Use numbers for categories in ordinal data
        if (is_ordinal(dv.metadata['dtype'])):
            numeric = [dv.metadata['categories'][x] for x in val]
            val = numeric
        data.append(val)

    return stats.wilcoxon(data[0], data[1])

# https://docs.scipy.org/doc/scipy-0.14.0/reference/generated/scipy.stats.pearsonr.html
# Parameters: x (array-like) | y (array-like)
def pearson_corr(iv: VarData, dv: VarData, predictions: list, comp_data: CombinedData, **kwargs):
    assert(len(comp_data.dataframes) == 2)

    data = []
    for key, val in comp_data.dataframes.items():
        data.append(val)

    return stats.pearsonr(data[0], data[1])


# https://docs.scipy.org/doc/scipy-0.14.0/reference/generated/scipy.stats.spearmanr.html
# Parameters: a, b (b is optional) | axis (optional) 
def spearman_corr(iv: VarData, dv: VarData, predictions: list, comp_data: CombinedData, **kwargs):
    assert(len(comp_data.dataframes) == 2)

    data = []
    for key, val in comp_data.dataframes.items():
        # Use numbers for categories in ordinal data
        if (is_ordinal(dv.metadata['dtype'])):
            numeric = [dv.metadata['categories'][x] for x in val]
            val = numeric

        data.append(val)

    return stats.spearmanr(data[0], data[1])


# https://docs.scipy.org/doc/scipy-0.14.0/reference/generated/scipy.stats.linregress.html
# Parameters: x (array-like) | y (array-like)
def linear_regression(iv: VarData, dv: VarData, predictions: list, comp_data: CombinedData, **kwargs):
    import pdb; pdb.set_trace()
    return stats.linregress(iv.dataframe, dv.dataframe)
    

## NAIVE IMPLEMENTATION RIGHT NOW
# TODO: depending on ow linear constraing solver is implemented, may want to have two separate functions - 1) returns the name of the test/function and 2) get test with parameters, but not executed??
# Based on the properties of data, find the most appropriate test to conduct
# Return the test but do not execute
def find_test(dataset: Dataset, comp_data: CombinedData, iv, dv, predictions, design: Dict[str, str], **kwargs):
    # Two IV groups (only applies to nominal/ordinal IVs)
    if (len(comp_data.dataframes) == 2):
        if (is_nominal(iv.metadata['dtype']) and is_independent_samples(iv.metadata['var_name'], design)):
            if (is_numeric(dv.metadata['dtype']) and is_normal(comp_data, kwargs['alpha'])):
                return lambda : t_test_ind(iv, dv, predictions, comp_data, **kwargs)
            elif (is_numeric(dv.metadata['dtype']) or is_ordinal(dv.metadata['dtype'])):
                return lambda : mann_whitney_u(iv, dv, predictions, comp_data, **kwargs)
            elif (is_nominal(dv.metadata['dtype'])):
                raise AssertionError('Not sure if Fishers is the correct test here - what if have more than 2 x 2 table??')
                return lambda : fishers_exact(iv, dv, predictions, comp_data, **kwargs)
        elif (is_nominal(iv.metadata['dtype']) and is_dependent_samples(iv.metadata['var_name'], design)):
            if (is_numeric(dv.metadata['dtype']) and is_normal(comp_data, kwargs['alpha'])):
                return lambda : t_test_paired(iv, dv, predictions, comp_data, **kwargs)
            elif (is_numeric(dv.metadata['dtype']) or is_ordinal(dv.metadata['dtype'])):
                return lambda : wilcoxon_signed_rank(iv, dv, predictions, comp_data, **kwargs)
            elif (is_nominal(dv.metadata['dtype'])):
                raise AssertionError('Not sure if McNemar is the correct test here - what if have more than 2 x 2 table??')
        elif (is_numeric(iv.metadata['dtype'])): # OR MOVE TO/REPEAT in outer IF/ELSE for comp_data.dataframes == 1??
            if (is_numeric(dv.metadata['dtype'])):
                # Check normal distribution of both variables
                if (is_normal(comp_data, kwargs['alpha'], comp_data.dataframes[dv.metadata['var_name']])):
                    # Check homoscedasticity
                    if (comp_data.properties.var[1] < kwargs['alpha']): 
                        return lambda : linear_regression(iv, dv, predictions, comp_data, **kwargs)
                    else:  
                        return lambda : pearson_corr(iv, dv, predictions, comp_data, **kwargs)
                else: 
                    return lambda : spearman_corr(iv, dv, predictions, comp_data, **kwargs)
            elif (is_numeric(dv.metadata['dtype']) or is_ordinal(dv.metadata['dtype'])):
                return lambda : spearman_corr(iv, dv, predictions, comp_data, **kwargs)
            elif (is_nominal(dv.metadata['dtype'])):
                # TODO depends on the number of outcome categories for nominal variable
                raise AssertionError ('Not implemnted - simple logistic regression')
    elif (len(comp_data.dataframes) > 2):
        raise NotImplementedError
    else: 
        raise AssertionError('Trying to compare less than 1 variables....?')

                

# This is the function used to determine and then execute test based on CombinedData
def execute_test(dataset: Dataset, data_props: CombinedData, iv: VarData, dv: VarData, predictions: list, design: Dict[str,str]): 
    # For power we need sample size, effect size, alpha
    sample_size = 0
    # calculate sample size
    for df in data_props.dataframes:
        sample_size += len(data_props.dataframes[df])

    effect_size = design['effect size'] if ('effect size' in design) else [.2, .5, .8] # default range unless user defines
    
    alpha = design['alpha'] if ('alpha' in design) else .05
    
    # Find test
    stat_test = find_test(dataset, data_props, iv, dv, predictions, design, sample_size=sample_size, effect_size=effect_size, alpha=alpha)
    
    # Execute test
    if stat_test: 
        results = stat_test()
    else: 
        results = bootstrap()
    stat_test_name = results.__class__.__name__

    # Wrap results in ResData and return
    return ResData(iv=iv.metadata['var_name'], dv=dv.metadata['var_name'], test_name=stat_test_name, results=results, properties=data_props.properties, predictions=predictions)
    
# def bootstrap(data):
def bootstrap():
    print('Do something with incoming data')

