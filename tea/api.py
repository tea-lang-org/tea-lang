from numpy import isin
from tea.logging.tea_logger import TeaLogger
from tea.helpers.study_type_determiner import StudyTypeDeterminer
import pandas as pd

from tea.runtimeDataStructures.resultData import ResultData

from .build import (load_data, load_data_from_url, const,
                    ordinal, isordinal,
                    nominal, isnominal,
                    ratio, isratio,
                    interval, isinterval, isnumeric,
                    select, compare, relate, predict,
                    get_var_from_list
                    )
from .vardata_factory import VarDataFactory
import tea.helpers
import tea.runtimeDataStructures
import tea.z3_solver
from tea.helpers.constants.default_values import DEFAULT_ALPHA_PARAMETER
from tea.z3_solver.solver import set_mode
from tisane.variable import Measure
from tea.variable import Nominal, Ordinal, Ratio, Interval, Unit

from typing import Dict, List
from .global_vals import *
from pathlib import Path

# Set at start of programs
# Used across functions
dataset_path = ''
dataset_obj = None
dataset_id = None
vars_objs = []
study_design = None

# For variables dictionary
var_name = 'name'
var_dtype = 'data type'
var_categories = 'categories'
var_drange = 'range'

# Assumptions
# Stats properties
assumptions = dict()
alpha = DEFAULT_ALPHA_PARAMETER

all_results = dict()  # Used for multiple comparison correction

# For solver
MODE = 'strict'

study_type_determiner = StudyTypeDeterminer()


# For testing purposes
def download_data(url, file_name):
    return load_data_from_url(url, file_name)


# @sets global dataset_path and dataaset_obj (of type Dataset)
def data(file, key=None):
    global dataset_path, dataset_obj, dataset_id

    # Require that the path to the data must be a string or a Path object
    assert isinstance(file, (str, Path, pd.DataFrame))
    dataset_path = file
    dataset_id = key.name if key is not None else None


def define_variables(vars: List[Measure]):
    global vars_objs

    vars_objs = list()
    for var in vars:
        name = var.name
        if (isinstance(var, Nominal)):
            categories = var.categories
            v_obj = nominal(name, categories)
        elif (isinstance(var, Ordinal)):
            categories = var.ordered_cat
            v_obj = ordinal(name, categories)
        elif (isinstance(var, Interval)):
            drange = None
            if var.range is not None:
                drange = var[var_drange]
            v_obj = interval(name, drange)
        else:
            assert (isinstance(var, Ratio) or isinstance(var, Unit))
            drange = var.range if var.range is not None else None
            v_obj = ratio(name, drange)

        vars_objs.append(v_obj)


def __define_study(study_type, ivs_name, ivs, dvs_name, dvs, btw_subjs_lst, within_subjs_lst):
    study_dict = dict()
    study_dict['study type'] = study_type
    study_dict[ivs_name] = [var.name for var in ivs]
    study_dict[dvs_name] = [var.name for var in dvs]
    if btw_subjs_lst is not None:
        study_dict[btw_subj] = [subj.name for subj in btw_subjs_lst]
    if within_subjs_lst is not None:
        study_dict[within_subj] = [subj.name for subj in within_subjs_lst]
    __define_study_design(study_dict)


def define_experiment(independent_variables:list, dependent_variables: list, between_subjects: list = None, within_subjects: list = None):
    __define_study('experiment', 'independent variables', independent_variables, 'dependent variables', dependent_variables, between_subjects, within_subjects)

def define_observational_study(contributor_variables:list, outcome_variables: list, between_subjects: list = None, within_subjects: list = None):
    __define_study('observational study', 'contributor variables', contributor_variables, 'outcome variables', outcome_variables, between_subjects, within_subjects)


def __define_study_design(design: Dict[str, str]):
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
                        raise ValueError(
                            f"{b} CANNOT be a between subjects variable AND a within subjects variable. Can only be one or the other.")

    study_design = design

    # dataset_id = design[uid] if uid in design else None


'''
Parameters
-----------
false_postive_error_rate: alpha level
'''
def assume(groups_normally_distributed:list = None, false_positive_error_rate:float=0.05, mode=None, equal_variance:list = None):
    tea_logger = TeaLogger.get_logger()
    global alpha
    global assumptions
    global MODE

    if groups_normally_distributed != None and \
        (not isinstance(groups_normally_distributed, list) or \
        not all(isinstance(x, list) for x in groups_normally_distributed)):
        raise Exception('groups normally distributed must be a list of pairs')

    if groups_normally_distributed != None:
        assumptions['groups normally distributed'] = []
        for group in groups_normally_distributed:
            assumptions['groups normally distributed'].append(list(x.name for x in group))
    
    assumptions[alpha_keywords[1]] = false_positive_error_rate

    if equal_variance is not None:
        assumptions['equal variance'] = equal_variance

    if mode and mode == 'relaxed':
        MODE = mode
        tea_logger.log_info(f"\nRunning under {MODE.upper()} mode.\n")
        tea_logger.log_info(
            f"This means that user assertions will be checked. Should they fail, Tea will issue a warning but proceed as if user's assertions were true.")
    else:
        assert (mode == None or mode == 'strict')
        MODE = 'strict'
        tea_logger.log_info(f"\nRunning under {MODE.upper()} mode.\n")
        tea_logger.log_info(f"This means that user assertions will be checked. Should they fail, Tea will override user assertions.\n")


def hypothesize(vars:List[Measure], predictions: list = None):
    define_variables(vars=vars) # define variables globally by setting vars_objs
    vars_names = list(x.name for x in vars)
    return __hypothesize(vars_names, predictions)
    

def __hypothesize(vars: list, prediction: list = None):
    global dataset_path, vars_objs, study_design, dataset_obj, dataset_id
    global assumptions, all_results
    global MODE

    if isinstance(dataset_path, (str, Path)):
        assert (dataset_path)
    elif isinstance(dataset_path, pd.DataFrame):
        assert not dataset_path.empty
    else:
        raise ValueError(f"dataset_path must be DataFrame, str, or Path. Not: {type(dataset_path)}")
    assert (vars_objs)
    assert (study_design)
    dataset_obj = load_data(dataset_path, vars_objs, dataset_id)

    v_objs = []
    for v in vars:
        v_objs.append(get_var_from_list(v, vars_objs))  # may want to use Dataset instance method instead

    # Create and get back handle to AST node
    relationship = relate(v_objs, prediction)
    num_comparisons = len(relationship.predictions) if len(relationship.predictions) > 0 else 1 # use for multiple comparison correction

    # Interpret AST node, Returns ResultData object <-- this may need to change
    set_mode(MODE)
    study_type_determiner = StudyTypeDeterminer()
    vardata_factory = VarDataFactory(study_type_determiner)
    result = vardata_factory.create_vardata(dataset_obj, relationship, assumptions, study_design)
    
    if dataset_obj.data.empty:
        # If the the result is a dictionary of test names, which should only happen if the data is empty
        assert(isinstance(result, list))
        assert(dataset_obj.has_empty_data())
        return result

    # Else
    assert(isinstance(result, ResultData))
    # Make multiple comparison correction
    result.bonferroni_correction(num_comparisons)
    
    print(f"\n{result}")
    return result

    # Use assumptions and hypotheses for interpretation/reporting back to user
    # Make result human_readable
    # output = translate(result)

    # Give user output
    # return output


# TODO: Add relate and compare methods

# @param vars that user would like to relate
# @param stats_tests contains all the tests that the user would like
# @return properties that must be true in order to satisfy
# as many of the tests as possible
def divine_properties(vars: list, tests: list):
    global study_design

    v_objs = []
    for v in vars:
        v_objs.append(get_var_from_list(v, vars_objs))  # may want to use Dataset instance method instead

    relationship = relate(v_objs)

    # What kind of study are we analyzing?
    study_type = study_type_determiner.determine_study_type(vars, study_design)

    combined_data = None
    # Do we have a Bivariate analysis?
    if len(vars) == 2:
        combined_data = BivariateData(vars, study_type, alpha=float(assumptions['alpha']))
    else:  # Do we have a Multivariate analysis?
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



