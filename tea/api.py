from . import ast
from . import build
from . import evaluate

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

## For testing purposes
def download_data(url, name): 
    return load_data_from_url(url, name)

# Set at start of programs
# Used across functions
dataset_path = ''
dataset_obj = None
dataset_id = None
vars_objs = []
study_design = None
assumptions = None

# For study design dictionary
uid = 'key'

# For variables dictionary
var_name = 'name'
var_dtype = 'data type'
var_categories = 'categories'
var_drange = 'range'
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
            drange = var[var_drange]
            v_obj = interval(name, drange)

        vars_objs.append(v_obj)


def define_study_design(design: Dict[str, str]): 
    global study_design, dataset_id, uid

    study_design = design

    dataset_id = design[uid] if uid in design else None
    

def assume(assumptions: Dict[str, str]): 
    pass

def hypothesize(vars: list, prediction: str=None): 
    global dataset_path, vars_objs, study_design, dataset_obj, dataset_id

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
    result = evaluate(dataset_obj, relationship, study_design)
    import pdb; pdb.set_trace()

    # Use assumptions and hypotheses for interpretation/reporting back to user
    # Make result human_readable
    # output = translate(result)

    # Give user output
    # return output

## TODO: Add relate and compare methods


    

