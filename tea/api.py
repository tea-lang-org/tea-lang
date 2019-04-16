from tea.build import (load_data, load_data_from_url, const,
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
from tea.evaluate import evaluate
from tea.evaluate_helper_methods import determine_study_type, assign_roles
from tea.evaluate_data_structures import BivariateData, MultivariateData
from .solver import which_props
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
alpha = 0.01

all_results = {} # Used for multiple comparison correction

## For testing purposes
def download_data(url, name): 
    return load_data_from_url(url, name)

# @sets global dataset_path and dataaset_obj (of type Dataset)
def data(file, key=None): 
    global dataset_path, dataset_obj, dataset_id

    dataset_path = file
    dataset_id = key

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
            drange=None
            if var_drange in var: 
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

    # dataset_id = design[uid] if uid in design else None
    

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
    global assumptions, all_results

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
    # all_results[relationship] -- How to check for multiple comparison problem?
    print(f"\n{result}")
    return result


    # Use assumptions and hypotheses for interpretation/reporting back to user
    # Make result human_readable
    # output = translate(result)

    # Give user output
    # return output

## TODO: Add relate and compare methods

# @param vars that user would like to relate
# @param stats_tests contains all the tests that the user would like
# @return properties that must be true in order to satisfy
# as many of the tests as possible
def divine_properties(vars:list, tests:list):
    global study_design

    v_objs = []
    for v in vars: 
        v_objs.append(get_var_from_list(v, vars_objs)) # may want to use Dataset instance method instead
    
    relationship = relate(v_objs)

    # What kind of study are we analyzing?
    study_type = determine_study_type(vars, study_design)

    combined_data = None
    # Do we have a Bivariate analysis?
    if len(vars) == 2: 
        combined_data = BivariateData(vars, study_type, alpha=float(assumptions['alpha'])) 
    else: # Do we have a Multivariate analysis?
        combined_data = MultivariateData(vars, study_type, alpha=float(assumptions['alpha']))

    # test_to_properties, test_to_broken_properties = which_props(['mannwhitney_u', 'students_t'])
    test_to_properties, test_to_broken_properties = which_props(tests, vars)
    

    all_properties_are_satisfied = True
    for val in test_to_broken_properties.values():
        if val:
            all_properties_are_satisfied = False
            break

    if all_properties_are_satisfied:
        print(f"\nProperties for {tests[0]} and {tests[1]} are complementary.")
    else:
        print(f"\nProperties for {tests[0]} and {tests[1]} conflict.")

    # print(ps)
    import pprint
    pp = pprint.PrettyPrinter()

    # print("\nProperties for student's t test and Mann Whitney u test are complementary.")
    print("\nProperties:")
    pp.pprint(test_to_properties)
    print("\nProperties that could not be satisfied:")
    pp.pprint(test_to_broken_properties)
