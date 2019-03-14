from . import ast
from . import build
# from . import evaluate

from .build import (load_data, load_data_from_url, const,
                    ordinal, isordinal,
                    nominal, isnominal,
                    ratio, isratio,
                    interval, isinterval, isnumeric,
                    select, compare, relate, predict,
                    get_var_from_list
                    # , nominal, interval, ratio, load_data, model, 
                    # mean, median, standard_deviation, variance, kurtosis, skew, normality, frequency,
                    # between_experiment, within_experiment, mixed_experiment, model, equation,
                    # load_data_arrs, hypothesis, experiment_design
                   )
from .evaluate import evaluate
from typing import Dict
from .global_vals import *

# Set at start of programs
# Used across functions
dataset_path = ''
dataset_obj = None
dataset_id = None
vars_objs = []
study_design = None
assumptions = None

# For variables dictionary
var_name = 'name'
var_dtype = 'data type'
var_categories = 'categories'
var_drange = 'range'

# Assumptions
# Stats properties
assumptions = {}
alpha_keywords = ['Type I (False Positive) Error Rate', 'alpha']
alpha = 0.05

## For testing purposes
def download_data(url, name): 
    return load_data_from_url(url, name)

# @sets global dataset_path and dataaset_obj (of type Dataset)
def data(file): 
    global dataset_path, dataset_obj

    dataset_path = file

def define_variables(vars: Dict[str, str]):
    global vars_objs

    # reset the variables
    vars_objs = []

    for var in vars: 
        name = var['name']

        if (var[var_dtype] == 'nominal'): 
            categories = var[var_categories]
            v_obj = nominal(name, categories)
        elif (var[var_dtype] == 'ordinal'): 
            categories = var[var_categories]
            v_obj = ordinal(name, categories)
        elif (var[var_dtype] == 'interval'): 
            drange = var[var_drange]
            v_obj = interval(name, drange)
        else: 
            assert(var[var_dtype] == 'ratio')
            drange = var[var_drange] if var_drange in var else None
            v_obj = interval(name, drange)

        vars_objs.append(v_obj)


def define_study_design(design: Dict[str, str]): 
    global study_design, dataset_id, uid, alpha
    global btw_subj, within_subj

    # Check that variables are only assigned EITHER between OR within but NOT BOTH: 
    btw_vars = design[btw_subj] if btw_subj in design else None
    within_vars = design[within_subj] if within_subj in design else None

    if btw_vars: 
        for b in btw_vars: 
            if within_vars:
                for w in within_vars: 
                    if b == w: 
                        raise ValueError(f"{b} CANNOT be a between subjects variable AND a within subjects variable. Can only be one or the other.")
                    
    study_design = design

    dataset_id = design[uid] if uid in design else None
    

def assume(user_assumptions: Dict[str, str]): 
    global alpha, alpha_keywords
    global assumptions

    if alpha_keywords[0] in user_assumptions:
        if alpha_keywords[1] in user_assumptions:
            assert (float(user_assumptions[alpha_keywords[0]]) == float(user_assumptions[alpha_keywords[1]]))
    
    for keyword in alpha_keywords:
        if keyword in user_assumptions:
            alpha = float(user_assumptions[keyword])

    assumptions = user_assumptions
    assumptions[alpha_keywords[1]] = alpha

def hypothesize(vars: list, prediction: str=None): 
    global dataset_path, vars_objs, study_design, dataset_obj, dataset_id
    global assumptions

    assert(dataset_path)
    assert(vars_objs)
    assert(study_design)

    dataset_obj = load_data(dataset_path, vars_objs, dataset_id)

    v_objs = []
    for v in vars: 
        v_objs.append(get_var_from_list(v, vars_objs)) # may want to use Dataset instance method instead
    
    # Create and get back handle to AST node
    relationship = relate(v_objs, prediction)
    # Interpret AST node, Returns ResData object (?)
    result = evaluate(dataset_obj, relationship, assumptions, study_design)


    # Use assumptions and hypotheses for interpretation/reporting back to user
    # Make result human_readable
    # output = translate(result)

    # Give user output
    # return output

## TODO: Add relate and compare methods


    

