from tea.global_vals import *
from tea.ast import *
from tea.dataset import Dataset
from tea.evaluate_data_structures import VarData, CombinedData, BivariateData, MultivariateData, ResData
# from tea.solver import Tests, Assumptions

import attr
from typing import Any, Dict, List
from types import SimpleNamespace # allows for dot notation access for dictionaries
import copy

from scipy import stats # Stats library used
import statsmodels.api as sm
import statsmodels.formula.api as smf
from statsmodels.formula.api import ols
# import numpy as np # Use some stats from numpy instead
import pandas as pd
import bootstrapped as bs


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
def compute_normal_distribution(data):
    # norm_test = stats.normaltest(data, axis=0)
    # return (norm_test[0], norm_test[1])
    shapiro_test = stats.shapiro(data)
    return shapiro_test
    # TODO: may want to compute/find the best distribution if not normal
 
# @returns bootstrapped variance for @param data
def compute_variance(data): 
    return -1

# Levene test to test for equal variances - Leven is more robust to nonnormal data than Bartlett's test
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
def students_t(dataset, combined_data: BivariateData):
    # assert(len(predictions) == 1)

    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    x = xs[0]
    y = ys[0]
    cat = [k for k,v in x.metadata[categories].items()]
    data = []

    for c in cat: 
        cat_data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
        data.append(cat_data)
    
    return stats.ttest_ind(data[0], data[1], equal_var=True)

# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.ttest_ind.html
# Possible parameters: a, b : array | axis (without, over entire arrays) | equal_var (default is True) | nan_policy (optional) 
def welchs_t(dataset, combined_data: BivariateData):
    # assert(len(predictions) == 1)

    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    x = xs[0]
    y = ys[0]
    cat = [k for k,v in x.metadata[categories].items()]
    data = []

    for c in cat: 
        cat_data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
        data.append(cat_data)
    
    return stats.ttest_ind(data[0], data[1], equal_var=False)

# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.mannwhitneyu.html
# Paramters: x, y : array_like | use_continuity (default=True, optional - for ties) | alternative (p-value for two-sided vs. one-sided)
# def utest(iv: VarData, dv: VarData, predictions: list, comp_data: CombinedData, **kwargs):
def mannwhitney_u(dataset, combined_data: BivariateData):
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
    
    return stats.mannwhitneyu(data[0], data[1], alternative='two-sided')

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
def pearson_corr(dataset: Dataset, combined_data: CombinedData):
    assert(len(combined_data.vars) == 2)
    
    data = []
    for var in combined_data.vars: 
        var_data = get_data(dataset, var)
        data.append(var_data)

    assert(len(data) == 2)

    return stats.pearsonr(data[0], data[1])


# https://docs.scipy.org/doc/scipy-0.14.0/reference/generated/scipy.stats.spearmanr.html
# Parameters: a, b (b is optional) | axis (optional) 
def spearman_corr(dataset: Dataset, combined_data: CombinedData):
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
    return stats.spearmanr(data[0], data[1])

# https://docs.scipy.org/doc/scipy-0.15.1/reference/generated/scipy.stats.kendalltau.html
# Parameters: x (array-like) | y (array-like) : Arrays of rankings, of the same shape. If arrays are not 1-D, they will be flattened to 1-D.
def kendalltau_corr(dataset: Dataset, combined_data: CombinedData): 
    assert(len(combined_data.vars) == 2)
    
    data = []
    for var in combined_data.vars: 
        var_data = get_data(dataset, var)
        data.append(var_data)

    assert(len(data) == 2)

    return stats.kendalltau(data[0], data[1])

# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.chi2_contingency.html
# Parameters: observed (contingency table) | correction (bool for Yates' correction) | lambda (change statistic computed)
def chi_square(dataset: Dataset, combined_data: CombinedData): 
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
    return stats.chi2_contingency(contingency_table, correction=False)

# https://docs.scipy.org/doc/scipy-0.18.1/reference/generated/scipy.stats.fisher_exact.html#scipy.stats.fisher_exact
# Parmaters: table (2 x 2) | alternative (default='two-sided' optional)
def fishers_exact(dataset: Dataset, combined_data: CombinedData): 
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

    return stats.fisher_exact(contingency_table, alternative='two-sided')

def f_test(dataset: Dataset, combined_data: CombinedData): 
    
    # Construct formula
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()
    assert(len(xs) == 1)
    assert(len(ys) == 1)

    x = xs[0]
    y = ys[0]
    
    formula = ols(f"{y.metadata[name]} ~ C({x.metadata[name]})", data=dataset.data)
    model =formula.fit()
    return sm.stats.anova_lm(model, type=2)
    # import pdb; pdb.set_trace()
    # >>> moore_lm = ols('conformity ~ C(fcategory, Sum)*C(partner_status, Sum)',
                #  data=data).fit()
    # >>> table = sm.stats.anova_lm(moore_lm, typ=2) # Type 2 Anova DataFrame

def factorial_ANOVA(dataset: Dataset, combined_data: CombinedData): 
    return True

# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.kruskal.html
def kruskall_wallis(dataset: Dataset, combined_data: CombinedData): 
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
    
    return stats.kruskal(*data)

# https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.friedmanchisquare.html#scipy.stats.friedmanchisquare
def friedman(dataset: Dataset, combined_data: CombinedData): 
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
    
    return stats.friedmanchisquare(*data)


# https://docs.scipy.org/doc/scipy-0.14.0/reference/generated/scipy.stats.linregress.html
# Parameters: x (array-like) | y (array-like)
def linear_regression(iv: VarData, dv: VarData, predictions: list, comp_data: CombinedData, **kwargs):
    import pdb; pdb.set_trace()
    return stats.linregress(iv.dataframe, dv.dataframe)

# This is the function used to determine and then execute test based on CombinedData
def execute_test_old(dataset: Dataset, data_props: CombinedData, iv: VarData, dv: VarData, predictions: list, design: Dict[str,str]): 
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


__stat_test_to_function__ = {
    'students_t': students_t,
    'welchs_t': welchs_t,
    'kendalltau_corr' : kendalltau_corr,
    'spearman_corr' : spearman_corr,
    'chi_square' : chi_square,
    'fishers_exact' : fishers_exact,
    'mannwhitney_u' : mannwhitney_u,
    'f_test' : f_test,
    'kruskall_wallis' : kruskall_wallis,
    'friedman': friedman,
    'factorial_ANOVA': factorial_ANOVA
}

# Returns the function that has the @param name
def lookup_function(test_name): 
    if test_name in __stat_test_to_function__: 
        return __stat_test_to_function__[test_name]
    else: 
        raise ValueError(f"Cannot find the test:{test_name}")

def execute_test(dataset, combined_data: CombinedData, test):         
    # Get function handler
    test_func = lookup_function(test)

    # Execute the statistical test
    stat_result = test_func(dataset, combined_data)

    # Return results
    return stat_result
    

"""
def explanatory_strings_for_assumptions(assumptions: Assumptions) -> List[str]:
    explanation = []
    if assumptions & Assumptions.INDEPENDENT_OBSERVATIONS:
        explanation.append("Assumes independent observations.")
        assumptions &= ~Assumptions.INDEPENDENT_OBSERVATIONS

    if assumptions & Assumptions.NORMALLY_DISTRIBUTED_VARIABLES:
        explanation.append("Assumes samples are normally distributed.")
        assumptions &= ~Assumptions.NORMALLY_DISTRIBUTED_VARIABLES

    if assumptions & Assumptions.NORMALLY_DISTRIBUTED_DIFFERENCE_BETWEEN_VARIABLES:
        explanation.append("Assumes difference between paired values is normally distributed.")
        assumptions &= ~Assumptions.NORMALLY_DISTRIBUTED_DIFFERENCE_BETWEEN_VARIABLES

    if assumptions & Assumptions.SYMMETRICALLY_DISTRIBUTED_DIFFERENCE_BETWEEN_VARIABLES:
        explanation.append("Assumes difference between paired values is symmetrically distributed.")
        assumptions &= ~Assumptions.SYMMETRICALLY_DISTRIBUTED_DIFFERENCE_BETWEEN_VARIABLES

    if assumptions & Assumptions.SIMILAR_VARIANCES:
        explanation.append("Assumes samples have similar variances.")
        assumptions &= ~Assumptions.SIMILAR_VARIANCES

    if assumptions & Assumptions.LARGE_SAMPLE_SIZE:
        explanation.append("Assumes a large enough sample size.")
        assumptions &= ~Assumptions.LARGE_SAMPLE_SIZE

    if assumptions & Assumptions.VALUES_ARE_FREQUENCIES:
        explanation.append("Assumes values are frequencies (and not, e.g., percentages).")
        assumptions &= ~Assumptions.VALUES_ARE_FREQUENCIES

    if assumptions & Assumptions.PAIRED_OBSERVATIONS:
        explanation.append("Assumes observations are paired (e.g. within subjects).")
        assumptions &= ~Assumptions.PAIRED_OBSERVATIONS

    if assumptions & Assumptions.NO_OUTLIERS:
        explanation.append("Assumes there are no outliers in the data.")
        assumptions &= ~Assumptions.NO_OUTLIERS

    if assumptions & Assumptions.NO_OUTLIERS_IN_DIFFERENCE_BETWEEN_VARIABLES:
        explanation.append("Assumes there are no outliers in the difference between paired values.")
        assumptions &= ~Assumptions.NO_OUTLIERS_IN_DIFFERENCE_BETWEEN_VARIABLES

    if assumptions & Assumptions.LINEAR_RELATIONSHIP:
        explanation.append("Assumes there is a linear relationship between the variables.")
        assumptions &= ~Assumptions.LINEAR_RELATIONSHIP

    if assumptions & Assumptions.BIVARIATE_NORMAL_VARIABLES:
        explanation.append("Assumes the two variables have a bivariate normal distribution.")
        assumptions &= ~Assumptions.BIVARIATE_NORMAL_VARIABLES

    if assumptions & Assumptions.RELATED_SAMPLES:
        explanation.append("Assumes the samples come from related sources (e.g. within subjects).")
        assumptions &= ~Assumptions.RELATED_SAMPLES

    if assumptions & Assumptions.MONOTONIC_RELATIONSHIP:
        explanation.append("Assumes there is a monotonic relationship between the variables.")
        assumptions &= ~Assumptions.MONOTONIC_RELATIONSHIP

    if assumptions & Assumptions.ALL_VARIABLES_CONTINUOUS_OR_ORDINAL:
        explanation.append("Assumes all variables are continuous or ordinal.")
        assumptions &= ~Assumptions.ALL_VARIABLES_CONTINUOUS_OR_ORDINAL

    if assumptions & Assumptions.DEPENDENT_VARIABLE_CONTINUOUS_OR_ORDINAL:
        explanation.append("Assumes the dependent variable is continuous or ordinal.")
        assumptions &= ~Assumptions.DEPENDENT_VARIABLE_CONTINUOUS_OR_ORDINAL

    assert assumptions == Assumptions.NONE, \
        "Not all assumptions have a corresponding explanatory string: %s" % assumptions

    return explanation
"""