# Tea
from tea.global_vals import *
from tea.ast import DataType, LessThan, GreaterThan
from tea.runtimeDataStructures.dataset import Dataset
from tea.runtimeDataStructures.varData import VarData
from tea.runtimeDataStructures.combinedData import CombinedData
from tea.runtimeDataStructures.bivariateData import BivariateData
from tea.runtimeDataStructures.multivariateData import MultivariateData
from tea.runtimeDataStructures.testResult import TestResult

# Stats
from statistics import mean, stdev
from math import sqrt
from scipy import stats # Stats library used
from sklearn import preprocessing # for creating interaction effects
import statsmodels.api as sm
import statsmodels.formula.api as smf
from statsmodels.formula.api import ols

import pandas as pd
from statsmodels.stats.anova import AnovaRM
import bootstrapped.bootstrap as bs
import bootstrapped.stats_functions as bs_stats

# Other
import attr
from typing import Any, Dict, List
from types import SimpleNamespace # allows for dot notation access for dictionaries
from collections import namedtuple
from enum import Enum
import copy

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

# Helper methods for Interpreter (in evaluate.py)
# Compute properties about the VarData objects in @param vars using data in @param dataset
def compute_data_properties(dataset, vars_data: list):
    vars = copy.deepcopy(vars_data)

    for v in vars:
        v.properties[sample_size] = len(dataset.select(v.metadata[name]))
        if v.is_continuous(): 
            v.properties[distribution] = compute_distribution(dataset.select(v.metadata[name]))
            v.properties[variance] = compute_variance(dataset.select(v.metadata[name]))
        elif v.is_categorical(): 
            v.properties[num_categories] = len(v.metadata[categories])

            # For each group (where DV is continuous) is the data normal?

        else: 
            raise ValueError (f"Not supported data type: {v.metadata[data_type]}")

    return vars

# Add equal variance property to @param combined_data
def add_eq_variance_property(dataset, combined_data: CombinedData, study_type: str): 
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
    
    combined_data.properties[eq_variance] = None

    if cat_xs and cont_ys: 
        for y in ys:
            for x in xs: 
                cat = [k for k,v in x.metadata[categories].items()]
                for c in cat: 
                    data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
                    grouped_data.append(data)
                if isinstance(combined_data, BivariateData):
                    # Equal variance
                    eq_var = compute_eq_variance(grouped_data)
                    combined_data.properties[eq_variance] = eq_var
                elif isinstance(combined_data, MultivariateData):
                    combined_data.properties[eq_variance + '::' + x.metadata[name] + ':' + y.metadata[name]] = compute_eq_variance(grouped_data)
                else: 
                    raise ValueError(f"combined_data_data object is neither BivariateData nor MultivariateData: {type(combined_data)}")

# Independent vs. Paired?
def add_paired_property(dataset, combined_data: CombinedData, study_type: str, design: Dict[str, str]=None): # check same sizes are identical
    global paired
    
    x = None
    y = None
    combined_data.properties[paired] = False
    if isinstance(combined_data, BivariateData): 
        if study_type == experiment_identifier: 
            # Just need one variable to be Categorical and another to be Continuous (regardless of role) 
            x = combined_data.get_vars(iv_identifier) 
            y = combined_data.get_vars(dv_identifier) 
            
        else: # study_type == observational_identifier
            x = combined_data.get_vars(contributor_identifier)
            y = combined_data.get_vars(outcome_identifier)
        
        if x and y:
            assert (len(x) == len(y) == 1)
            x = x[0]
            y = y[0]

            if x.is_categorical() and y.is_continuous(): 
                if within_subj in design and design[within_subj] == x.metadata[name]:
                    combined_data.properties[paired] = True

def add_categories_normal(dataset, combined_data: CombinedData, study_type: str, design: Dict[str, str]=None): 
    global cat_distribution

    xs = None
    ys = None
    cat_xs = []
    cont_ys = []
    grouped_data = dict()

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

    combined_data.properties[cat_distribution] = None

    if cat_xs and cont_ys: 
        for y in ys:
            for x in xs: 
                cat = [k for k,v in x.metadata[categories].items()]
                for c in cat: 
                    data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
                    grouped_data_name =  str(x.metadata[name] + ':' + c)
                    grouped_data[grouped_data_name] = compute_distribution(data)
                combined_data.properties[cat_distribution] = dict()
                combined_data.properties[cat_distribution][y.metadata[name] + '::' + x.metadata[name]] = grouped_data

# Compute properties that are between/among VarData objects
def compute_combined_data_properties(dataset, combined_data: CombinedData, study_type: str, design: Dict[str, str]=None):
    assert (study_type == experiment_identifier or study_type == observational_identifier)
    combined = copy.deepcopy(combined_data)

    # Equal variance?
    add_eq_variance_property(dataset, combined, study_type)

    # Independent vs. Paired?
    add_paired_property(dataset, combined, study_type, design) # check sample sizes are identical

    # Add is_normal for every category? in dictionary
    add_categories_normal(dataset, combined, study_type, design)

    return combined

# Check normality of data
# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.normaltest.html
# Based on D’Agostino, R. B. (1971), “An omnibus test of normality for moderate and large sample size”, Biometrika, 58, 341-348
# and D’Agostino, R. and Pearson, E. S. (1973), “Tests for departure from normality”, Biometrika, 60, 613-622
# Null hypothesis is that distribution comes from Normal Distribution
# Rejecting null means that distribution is NOT normal

## CHANGED TO SHAPIRO TEST
# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.shapiro.html
# Null hypothesis is that distribution comes from normal distribution.
NormalTest = namedtuple('NormalTest', ('W', 'p_value'))

def compute_normal_distribution(data):
    # norm_test = stats.normaltest(data, axis=0)
    # return (norm_test[0], norm_test[1])
    w, p_value = stats.shapiro(data)
    return NormalTest(w, p_value)
    # TODO: may want to compute/find the best distribution if not normal
 
# @returns bootstrapped variance for @param data
def compute_variance(data): 
    return -1

# Levene test to test for equal variances - Levene is more robust to nonnormal data than Bartlett's test
# Null Hypothesis is that samples have the same variances
# Rejecting null means that samples have different variances
# TODO: ??? Default/currently using .05 alpha level
# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.levene.html#scipy.stats.levene

def compute_eq_variance(groups_data):
    levene_test = stats.levene(*groups_data)
    return (levene_test[0], levene_test[1])

# Queries dataset using var_data's query
# @returns data for var_data according to its internally held query
def get_data(dataset: Dataset, var: VarData):
    return dataset.select(var.metadata[name], where=f"{var.metadata[query]}")

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
# StudentsTResult = namedtuple('StudentsTResult', ('statistic', 'p', 'adjusted_p')) #, 'interpretation'))
def students_t(dataset, predictions, combined_data: BivariateData):

    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    x = xs[0]
    y = ys[0]
    cat = [k for k,v in x.metadata[categories].items()]
    data = []

    if predictions: 
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None
    
    lhs = None
    rhs = None
    for c in cat: 
        cat_data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
        if c == prediction.lhs.value:
            lhs = cat_data
        if c == prediction.rhs.value:
            rhs = cat_data
        data.append(cat_data)

    t_stat, p_val = stats.ttest_ind(lhs, rhs, equal_var=True)

    group_descriptive_statistics = {
        prediction.lhs.value: {
            'mean': mean(lhs),
            'stdev': stdev(lhs),
        }, prediction.rhs.value: {
            'mean': mean(rhs),
            'stdev': stdev(rhs),
        },
    }
    
    dof = len(lhs) + len(rhs) - 2 # Group1 + Group2 - 2
    test_result = TestResult( 
                        name = students_t_name,
                        test_statistic = t_stat,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha,
                        x = x,
                        y = y,
                        group_descriptive_statistics=group_descriptive_statistics)

    return test_result
    

# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.ttest_rel.html#scipy.stats.ttest_rel
# Possible parameters: a, b : array | axis (without, over entire arrays) | nan_policy (optional) 
def paired_students_t(dataset, predictions, combined_data: CombinedData): 
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    x = xs[0]
    y = ys[0]
    cat = [k for k,v in x.metadata[categories].items()]
    data = []
    
    if predictions: 
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None

    for c in cat: 
        cat_data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
        data.append(cat_data)
    
    t_stat, p_val = stats.ttest_rel(data[0], data[1])
    dof = (len(data[0]) + len(data[1]))/2. - 1 # (Group1 + Group2)/2 - 1
    test_result = TestResult( 
                        name = paired_students_name,
                        test_statistic = t_stat,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha,
                        x = x,
                        y = y)

    return test_result


# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.ttest_ind.html
# Possible parameters: a, b : array | axis (without, over entire arrays) | equal_var (default is True) | nan_policy (optional) 
def welchs_t(dataset, predictions, combined_data: BivariateData):
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    x = xs[0]
    y = ys[0]
    cat = [k for k,v in x.metadata[categories].items()]
    data = []

    for c in cat: 
        cat_data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
        data.append(cat_data)
    

    if predictions: 
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None
    t_stat, p_val = stats.ttest_ind(data[0], data[1], equal_var=False)
    # dof = (len(data[0]) + len(data[1]))/2. - 1 # (Group1 + Group2)/2 - 1
    
    # TODO Maybe use Satterthaite-Welch adjustment 
    if len(data[0]) < len(data[1]): 
        dof = len(data[0]) - 1
    else: 
        dof = len(data[1]) - 1
    test_result = TestResult( 
                        name = welchs_t_name,
                        test_statistic = t_stat,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha,
                        x = x,
                        y = y)

    return test_result


# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.mannwhitneyu.html
# Paramters: x, y : array_like | use_continuity (default=True, optional - for ties) | alternative (p-value for two-sided vs. one-sided)
# def utest(iv: VarData, dv: VarData, predictions: list, comp_data: CombinedData, **kwargs):
def mannwhitney_u(dataset, predictions, combined_data: BivariateData):
    assert (len(combined_data.vars) == 2)
    assert (len(combined_data.get_explanatory_variables()) == 1)
    assert (len(combined_data.get_explained_variables()) == 1)

    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    x = xs[0]
    y = ys[0]
    cat = [k for k,v in x.metadata[categories].items()]
    data = []

    for c in cat: 
        cat_data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
        data.append(cat_data)
    
    if predictions: 
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None
    t_stat, p_val = stats.mannwhitneyu(data[0], data[1], alternative='two-sided')
    dof = len(data[0]) # TODO This might not be correct
    test_result = TestResult( 
                        name = mann_whitney_name,
                        test_statistic = t_stat,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha,
                        x = x,
                        y = y)

    return test_result


# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.wilcoxon.html
# Parameters: x (array-like) | y (array-like, optional) | zero_method (default = 'wilcox', optional) | correction (continuity correction, optional)
def wilcoxon_signed_rank(dataset: Dataset, predictions, combined_data: CombinedData):
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    x = xs[0]
    y = ys[0]
    cat = [k for k,v in x.metadata[categories].items()]
    data = []

    for c in cat: 
        cat_data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
        data.append(cat_data)
    
    if predictions: 
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None
    t_stat, p_val = stats.wilcoxon(data[0], data[1])
    dof = len(data[0]) # TODO This might not be correct
    test_result = TestResult( 
                        name = wilcoxon_signed_rank_name,
                        test_statistic = t_stat,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha,
                        x = x,
                        y = y)

    return test_result


# https://docs.scipy.org/doc/scipy-0.14.0/reference/generated/scipy.stats.pearsonr.html
# Parameters: x (array-like) | y (array-like)
def pearson_corr(dataset: Dataset, predictions, combined_data: CombinedData):
    assert(len(combined_data.vars) == 2)
    
    data = []
    for var in combined_data.vars: 
        var_data = get_data(dataset, var)
        data.append(var_data)

    assert(len(data) == 2)
    
    if predictions: 
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None
    t_stat, p_val = stats.pearsonr(data[0], data[1])
    dof = None
    test_result = TestResult( 
                        name = pearson_name,
                        test_statistic = t_stat,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha)
    return test_result


# https://docs.scipy.org/doc/scipy-0.14.0/reference/generated/scipy.stats.spearmanr.html
# Parameters: a, b (b is optional) | axis (optional) 
def spearman_corr(dataset: Dataset, predictions, combined_data: CombinedData):
    assert(len(combined_data.vars) == 2)
    
    data = []
    for var in combined_data.vars: 
        # TODO: Check that var is ordinal. If so, then assign all ordinal values numbers 
        # Compare to without converting to numbers (in Evernote)
        var_data = get_data(dataset, var)
        if var.is_ordinal(): 
            ordered_cat = var.metadata[categories]
            num_var_data = [ordered_cat[v] for v in var_data]
            var_data = num_var_data

        data.append(var_data)
    
    assert(len(data) == 2)

    if predictions: 
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None
    t_stat, p_val = stats.spearmanr(data[0], data[1])
    dof = None
    test_result = TestResult( 
                        name = spearman_name,
                        test_statistic = t_stat,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha)
    return test_result

# https://docs.scipy.org/doc/scipy-0.15.1/reference/generated/scipy.stats.kendalltau.html
# Parameters: x (array-like) | y (array-like) : Arrays of rankings, of the same shape. If arrays are not 1-D, they will be flattened to 1-D.
def kendalltau_corr(dataset: Dataset, predictions, combined_data: CombinedData): 
    assert(len(combined_data.vars) == 2)
    
    data = []
    for var in combined_data.vars: 
        var_data = get_data(dataset, var)
        data.append(var_data)

    assert(len(data) == 2)
    if predictions: 
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None
    t_stat, p_val = stats.kendalltau(data[0], data[1])
    dof = None
    test_result = TestResult( 
                        name = kendalltau_name,
                        test_statistic = t_stat,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha)

    return test_result

def pointbiserial(dataset: Dataset, predictions, combined_data: CombinedData): 
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()

    assert(len(xs) == 1)
    assert(len(ys) == 1)
    x = xs[0]
    y = ys[0]
    cat = [k for k,v in x.metadata[categories].items()]
    data = []

    for c in cat: 
        cat_data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
        data.append(cat_data)

    if predictions: 
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None
    t_stat, p_val = stats.pointbiserialr(data[0], data[1])
    dof = None
    test_result = TestResult( 
                        name = pointbiserial_name,
                        test_statistic = t_stat,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha)
    
    return test_result

    
# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.chi2_contingency.html
# Parameters: observed (contingency table) | correction (bool for Yates' correction) | lambda (change statistic computed)
# ChisquareResult = namedtuple('ChisquareResult', ('chi2', 'p', 'dof', 'expected'))

def chi_square(dataset: Dataset, predictions, combined_data: CombinedData): 
    # Compute the contingency table
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    if len(xs) == 1: 
        if len(ys) == 1: 
            x = xs[0]
            y = ys[0]

            # Get the count for each category
            x_cat = [k for k,v in x.metadata[categories].items()]
            y_cat = [k for k,v in y.metadata[categories].items()]

            contingency_table = []
            contingency_table_key = [] # labels for the order in which data is stored in data array (define above)

            for xc in x_cat: 
                table_row = []
                table_row_key = []
                for yc in y_cat: 
                    data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{xc}'", f"{y.metadata[name]} == '{yc}'"])
                    table_row.append(len(data))

                    x_y_key = str(x.metadata[name]) + ':' + str(xc) + ' by ' + str(y.metadata[name]) + ':' + str(yc)
                    table_row_key.append(x_y_key)
                
                assert(len(table_row_key) == len(table_row))
                assert(len(table_row) == len(y_cat))
                contingency_table.append(table_row)
                contingency_table_key.append(table_row_key)
            
        else: 
            raise ValueError(f"Currently, chi square requires/only supports 1 explained variable, instead received: {len(ys)} -- {ys}")    
    else: 
        raise ValueError(f"Currently, chi square requires/only supports 1 explanatory variable, instead received: {len(xs)} -- {xs}")

    # chi2, p, dof, ex = chi2_contingency(obs, correction=False)
    # chi2, p, dof, ex = stats.chi2_contingency(contingency_table, correction=False)

    if predictions: 
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None
    test_statistic, p_val, dof, ex = stats.chi2_contingency(contingency_table, correction=False)
    dof = None
    test_result = TestResult( 
                        name = chi_square_name,
                        test_statistic = test_statistic,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha,
                        x = x,
                        y = y)
    
    return test_result
    

# https://docs.scipy.org/doc/scipy-0.18.1/reference/generated/scipy.stats.fisher_exact.html#scipy.stats.fisher_exact
# Parmaters: table (2 x 2) | alternative (default='two-sided' optional)
# FishersResult = namedtuple('FishersResult', ('oddsratio', 'p_value'))

def fishers_exact(dataset: Dataset, predictions, combined_data: CombinedData): 
    assert(len(combined_data.vars) == 2)

    # Compute the contingency table
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    assert(len(xs) == 1)
    assert(len(ys) == 1)

    x = xs[0]
    y = ys[0]

    # Get the count for each category
    x_cat = [k for k,v in x.metadata[categories].items()]
    y_cat = [k for k,v in y.metadata[categories].items()]

    contingency_table = []
    contingency_table_key = [] # labels for the order in which data is stored in data array (define above)

    for xc in x_cat: 
        table_row = []
        table_row_key = []
        for yc in y_cat: 
            data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{xc}'", f"{y.metadata[name]} == '{yc}'"])
            table_row.append(len(data))

            x_y_key = str(x.metadata[name]) + ':' + str(xc) + ' by ' + str(y.metadata[name]) + ':' + str(yc)
            table_row_key.append(x_y_key)
        
        assert(len(table_row_key) == len(table_row))
        assert(len(table_row) == len(y_cat))
        contingency_table.append(table_row)
        contingency_table_key.append(table_row_key)

    # odds_ratio, p_value = stats.fisher_exact(contingency_table, alternative='two-sided')
    # return FishersResult(odds_ratio, p_value)

    if predictions: 
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None
    odds_ratio, p_val = stats.fisher_exact(contingency_table, alternative='two-sided')
    dof = None
    test_result = TestResult( 
                        name = fisher_exact_name,
                        test_statistic = odds_ratio,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha,
                        x = x,
                        y = y)
    
    return test_result

def f_test(dataset: Dataset, predictions, combined_data: CombinedData):  
    # Construct formula
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    assert(len(xs) == 1)
    assert(len(ys) == 1)

    x = xs[0]
    y = ys[0]
    
    formula = ols(f"{y.metadata[name]} ~ C({x.metadata[name]})", data=dataset.data)
    model =formula.fit()
    

    if predictions:
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None
    result_df = sm.stats.anova_lm(model, type=2)
    # Need to inspect the result_df and return the appropriate test_statistic/p_value pair based on the prediction
    col_name = "C(" + x.metadata[name] + ")"
    for row_name in result_df.index: 
        if row_name == col_name: 
            row_data = result_df.loc[row_name]
            test_statistic = row_data['F']
            p_val = row_data['PR(>F)']
            dof = row_data['df']

    test_result = TestResult( 
                        name = f_test_name,
                        test_statistic = test_statistic,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha,
                        table = result_df,
                        x=x,
                        y=y)
    
    return test_result


# Private function to prevent duplicate symmetric interactions
# (e.g., ''A*B' is the same as 'B*A', both should not occur in ANOVA formula twice)
def _is_interaction_unique(interactions, inter):
    for existing_inter in interactions: 
        variables = inter.split('*')
        # Check if the varibles in inter already exist in another interaction
        exists = [(v in existing_inter) for v in variables]
        # If all of the variables in inter already exist, this means 
        # the interaction is not unique!
        return not all(exists)
        
def factorial_ANOVA(dataset: Dataset, predictions, combined_data: CombinedData): 

    # Construct formula
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    assert(len(ys) == 1)

    y = ys[0]
    
    formula = f"{y.metadata[name]} ~ "

    for i in range(len(xs)): 
        x = xs[i]
        formula += f"C({x.metadata[name]})"

        if i < len(xs) - 1: 
            formula += " + "
    
    
    # Add the interactions
    interactions = []
    for i in range(len(xs)): 
        x_i = xs[i]
        inter = f"C({x_i.metadata[name]})" 
        for j in range(len(xs)):
            if i != j: 
                x_j = xs[j]
                inter += " * " + f"C({x_j.metadata[name]})"
                interactions.append(inter)
                
                if _is_interaction_unique(interactions, inter):
                    formula += " + " +  inter

    ols_formula = ols(formula, data=dataset.data)
    model = ols_formula.fit()
    result_df = sm.stats.anova_lm(model, type=2)
    if predictions:
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None

    col_name = "C(" + x.metadata[name] + ")"
    for row_name in result_df.index: 
        if row_name == col_name: 
            row_data = result_df.loc[row_name]
            test_statistic = row_data['F']
            p_val = row_data['PR(>F)']
            dof = row_data['df']

    test_result = TestResult(
                        name = factorial_anova_name,
                        test_statistic = test_statistic,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha,
                        table = result_df,
                        y = y,
                        x = xs[0])
    
    return test_result

def rm_one_way_anova(dataset: Dataset, predictions, design, combined_data: CombinedData): 
    data = dataset.data
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()

    assert(len(ys) == 1)
    y = ys[0]
    between_subjs = []
    within_subjs = []
    for x in xs: 
        if "between subjects" in design and design["between subjects"] == x.metadata[name]:
            between_subjs.append(x.metadata[name])
        if "within subjects" in design and design["within subjects"] == x.metadata[name]:
            within_subjs.append(x.metadata[name])
    
    if predictions:
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None

    key = dataset.pid_col_name
    aovrm2way = AnovaRM(data, depvar=y.metadata[name], subject=key, within=within_subjs, aggregate_func='mean')
    # aovrm2way = AnovaRM(data, depvar=y.metadata[name], subject=dataset.pid_col_name, within=within_subjs, between=between_subjs) # apparently not implemented in statsmodels
    res2way = aovrm2way.fit()
    result_df = res2way.anova_table

    col_name = x.metadata[name]
    for row_name in result_df.index: 
        if row_name == col_name: 
            row_data = result_df.loc[row_name]
            test_statistic = row_data['F Value']
            p_val = row_data['Pr > F']
            dof = (row_data['Num DF'], row_data['Den DF'])

    test_result = TestResult( 
                        name = rm_one_way_anova_name,
                        test_statistic = test_statistic,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha,
                        table = result_df,
                        x = x,
                        y = y)
    
    return test_result

# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.kruskal.html
def kruskall_wallis(dataset: Dataset, predictions, combined_data: CombinedData): 
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    assert (len(ys) == 1)
    y = ys[0]

    data = []
    for x in xs: 
        if x.metadata[categories] is None: 
            raise ValueError('')
        cat = [k for k,v in x.metadata[categories].items()]
        for c in cat: 
            cat_data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
            data.append(cat_data)
    
    if predictions: 
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None
    t_stat, p_val = stats.kruskal(*data)
    dof = len(data[0]) # TODO This might not be correct
    test_result = TestResult( 
                        name = kruskall_wallis_name,
                        test_statistic = t_stat,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha,
                        x = xs[0], # TODO: Not sure if it's possible to have multiple x's?
                        y = y)
    
    return test_result
    # return TestResult('Kruskal Wallis', result.statistic, result.pvalue)


# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.friedmanchisquare.html#scipy.stats.friedmanchisquare
def friedman(dataset: Dataset, predictions, combined_data: CombinedData): 
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    assert (len(ys) == 1)
    y = ys[0]

    data = []
    for x in xs: 
        cat = [k for k,v in x.metadata[categories].items()]
        for c in cat: 
            cat_data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
            data.append(cat_data)
    
    # return stats.friedmanchisquare(*data)

    if predictions: 
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None
    test_statistic, p_val = stats.friedmanchisquare(*data)
    dof = len(data[0]) # TODO This might not be correct
    test_result = TestResult( 
                        name = "Kruskall Wallis Test",
                        test_statistic = test_statistic,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha)
    
    return test_result
    


# https://docs.scipy.org/doc/scipy-0.14.0/reference/generated/scipy.stats.linregress.html
# Parameters: x (array-like) | y (array-like)
def linear_regression(iv: VarData, dv: VarData, predictions: list, comp_data: CombinedData, **kwargs):
    # import pdb; pdb.set_trace()
    return stats.linregress(iv.dataframe, dv.dataframe)
    
# def bootstrap(data):
def bootstrap(dataset: Dataset, predictions, combined_data: CombinedData):
    calculations = {}

    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()

    for y in ys: 
        # for now
        assert(len(ys) == 1)
        
        # Main effects
        for x in xs: 
            cat = [k for k,v in x.metadata[categories].items()]
            for c in cat: 
                cat_data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
                stat = bs.bootstrap(cat_data.to_numpy(), stat_func=bs_stats.median)
                calculations[c] = stat
        
    if predictions: 
        if isinstance(predictions[0], list): 
            prediction = predictions[0][0]
        else: 
            prediction = predictions[0]
    else: 
        prediction = None

    x = xs[0] # We should do this for the prediction, only....?
    cat = [k for k,v in x.metadata[categories].items()]
    test_statistic = {}
    p_val = None
    for c in cat: 
        # import pdb; pdb.set_trace()
        lb = calculations[c].lower_bound
        ub = calculations[c].upper_bound

        test_statistic[c] = (lb, ub)

    alpha = combined_data.alpha
    lb = None
    ub = None
    for group, bounds in test_statistic.items(): 
        if not lb:
            assert(not ub)
            lb = bounds[0]
            ub = bounds[1]
        else: 
            if bounds[0] >= lb and bounds[0] <= ub: 
                p_val = f'Greater than or equal to {alpha}'
            elif bounds[1] >= lb and bounds[1] <=ub:  
                p_val = f'Greater than or equal to {alpha}'
            else: 
                p_val = f'Less than {alpha}'

    dof = None
    test_result = TestResult( 
                        name = "Bootstrap",
                        test_statistic = test_statistic,
                        p_value = p_val,
                        prediction = prediction,
                        dof = dof,
                        alpha = combined_data.alpha,
                        table = calculations)
    
    return test_result
    

def cohens(dataset, predictions, combined_data: CombinedData): 
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    x = xs[0]
    y = ys[0]
    cat = [k for k,v in x.metadata[categories].items()]
    data = []

    pred = None
    if predictions:
        pred = predictions[0][0]
    
    lhs = None
    rhs = None
    for c in cat: 
        cat_data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
        if c == pred.lhs.value:
            lhs = cat_data
        if c == pred.rhs.value:
            rhs = cat_data
        data.append(cat_data)
    
    cohens_d = (mean(lhs) - mean(rhs)) / (sqrt((stdev(lhs) ** 2 + stdev(rhs) ** 2) / 2))
    return cohens_d

def vda(dataset, predictions, combined_data: CombinedData): 
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    x = xs[0]
    y = ys[0]
    cat = [k for k,v in x.metadata[categories].items()]
    data = []

    pred = None
    if predictions:
        pred = predictions[0][0]
    
    lhs = None
    rhs = None
    for c in cat: 
        cat_data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
        if c == pred.lhs.value:
            lhs = cat_data
        if c == pred.rhs.value:
            rhs = cat_data
        data.append(cat_data)

    
    m = len(lhs)
    n = len(rhs)
    concat = lhs.append(rhs)
    r = stats.rankdata(concat)
    r1 = sum(r[range(0,m)])
  
    # Compute the measure
    # A = (r1/m - (m+1)/2)/n # formula (14) in Vargha and Delaney, 2000
    A = (2*r1 - m*(m+1)) / (2*n*m) # equivalent formula to avoid accuracy errors
    return A

__stat_test_to_function__ = {
    'pearson_corr' : pearson_corr,
    'kendalltau_corr' : kendalltau_corr,
    'spearman_corr' : spearman_corr,
    'pointbiserial_corr_a': pointbiserial,
    'pointbiserial_corr_b': pointbiserial,
    
    'students_t': students_t, # cohen's d, A12
    'welchs_t': welchs_t, # A12
    'mannwhitney_u' : mannwhitney_u, # A12
    'paired_students_t' : paired_students_t, # cohen's d, A12
    'wilcoxon_signed_rank' : wilcoxon_signed_rank, # A12

    'chi_square' : chi_square,
    'fishers_exact' : fishers_exact,
    
    'f_test' : f_test,
    'kruskall_wallis' : kruskall_wallis,
    'friedman': friedman,
    'factorial_ANOVA': factorial_ANOVA,
    'rm_one_way_anova': rm_one_way_anova,

    'bootstrap': bootstrap
}

# Returns the function that has the @param name
def lookup_function(test_name): 
    if test_name in __stat_test_to_function__: 
        return __stat_test_to_function__[test_name]
    else: 
        raise ValueError(f"Cannot find the test:{test_name}")

def add_effect_size(dataset, predictions, combined_data, test_func, stat_result):   
    parametric_tests =[students_t, paired_students_t]
    nonparametric_tests = [welchs_t, mannwhitney_u, wilcoxon_signed_rank]
    added_effect_size = False

    if test_func in parametric_tests: 
        # Calculate Cohen's d
        d = cohens(dataset, predictions, combined_data)
        stat_result.add_effect_size('Cohen\'s d', d)
        added_effect_size = True
    if test_func in parametric_tests or test_func in nonparametric_tests: 
        # Calculate A12
        a12 = vda(dataset, predictions, combined_data)
        stat_result.add_effect_size('A12', a12)
        added_effect_size = True

    if added_effect_size:
        stat_result.add_effect_size_to_interpretation()

def add_dof(dataset, predictions, combined_data, test_func, stat_result): 
    import pdb; pdb.set_trace()

def execute_test(dataset, design, predictions, combined_data: CombinedData, test):         
    # Get function handler
    test_func = lookup_function(test)

    # Execute the statistical test
    if test_func is rm_one_way_anova: 
        stat_result = test_func(dataset, predictions, design, combined_data)
    else:
        stat_result = test_func(dataset, predictions, combined_data)

    # Calculate the effect size
    add_effect_size(dataset, predictions, combined_data, test_func, stat_result)

    # Compute the DOF
    # add_dof(dataset, predictions, combined_data, test_func, stat_result)

    # Return results
    return stat_result

#
# # Correct for multiple comparisons
# def correct_multiple_comparison(res_data: ResultData, num_comparisons: int):
#     # TODO: refactor ResultData first.
#     res_data.adjust_p_values(num_comparisons)
