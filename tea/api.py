from tea.logging.tea_logger import TeaLogger
from tea.helpers.study_type_determiner import StudyTypeDeterminer
import pandas as pd

from .build import (
    load_data,
    load_data_from_url,
    const,
    ordinal,
    isordinal,
    nominal,
    isnominal,
    ratio,
    isratio,
    interval,
    isinterval,
    isnumeric,
    select,
    compare,
    relate,
    predict,
    get_var_from_list,
)
from .vardata_factory import VarDataFactory
import tea.helpers
import tea.runtimeDataStructures
import tea.z3_solver
from tea.helpers.constants.default_values import DEFAULT_ALPHA_PARAMETER
from tea.z3_solver.solver import set_mode

from tea.runtimeDataStructures.dataset import Dataset
from tea.runtimeDataStructures.variable import AbstractVariable, NominalVariable, OrdinalVariable, NumericVariable
from tea.runtimeDataStructures.design import AbstractDesign, ObservationalDesign, ExperimentDesign
from tea.runtimeDataStructures.hypothesis import AbstractHypothesis, LinearHypothesis, GroupComparisons

from typing import Dict
# from .global_vals import *
from pathlib import Path
from enum import Enum

class Mode(Enum): 
    STRICT_MODE = "STRICT" # Check user assumptions, if fail to validate, terminate program/analysis
    INFER_MODE = "INFER" # DEFAULT: Infer all properties about data, not require user assumptions
    RELAXED_MODE = "RELAXED" # Check user assumptions, if fail to validate, proceed with user assumptions (as if they passed)

# Public facing Tea object end-user can construct
class Tea(object):
    data: None
    variables: list # list of AbstractVariable
    design: AbstractDesign
    hypothesis: AbstractHypothesis
    mode: str

    def __init__(self, data_source = None, variables = None, design = None, assumptions = None, mode = Mode.INFER_MODE): 
        # Initialize to None
        self.data = None
        self.variables = None
        self.design = None
        self.hypothesis = None 
        
        # Mutate with any user-specified values
        if not data_source is None: 
            self.add_data(data_source)
        if not variables is None: 
            self.declare_variables(variables)
        if not design is None:
            self.specify_design(design)
        if not assumptions is None: 
            self.assume(assumptions, self.variables) # Assume updates Variables
        self.mode = mode

    def add_data(self, data_source): 
        data_obj = Dataset(data_source)
        
        self.data = data_obj

    def declare_variables(self, variables: Dict[str, str]):
        # List of Variables
        var_objs = []

        for var in variables:
            var_obj = AbstractVariable.create(var)
            var_objs.append(var_obj)

        self.variables = var_objs

    def specify_design(self, design: Dict[str, str]):
        design_obj = AbstractDesign.create(design, self.variables)

        self.design = design_obj

    def assume(self, assumptions: Dict[str, str], variables):
        for key, value in assumptions.items():
            if isinstance(value, list):
                for v in value:
                    var = AbstractVariable.get_variable(variables, v)
                    if var:
                        var.assume(key)
            else:
                var = AbstractVariable.get_variable(variables, value)
                if var:
                    var.assume(key)

    def hypothesize(self, hypothesis):
        hypothesis_obj = AbstractHypothesis.create(hypothesis, self.variables, self.design)

        self.hypothesis = hypothesis_obj # What if this adds hypotheses to a list of Hypotheses?


    # IDEA: Maybe this executes end-user to add hypotheses (through several successive calls to hypothesize) and then execute all at once
    # to allow for correction of multiple comparisons. 
    # IMPLICATION: each call to hypothesize and execute should output/return to the end-user a list of current hypotheses
    def execute(self): 
        # Interpret AST node, Returns ResultData object <-- this may need to change
        study_type_determiner = StudyTypeDeterminer() # May no longer need this
        vardata_factory = VarDataFactory(study_type_determiner) # This may need to change
        result = vardata_factory.create_vardata(dataset_obj, relationship, assumptions, study_design)

        # Make multiple comparison correction
        result.bonferroni_correction(num_comparisons)

        print(f"\n{result}")
        # return result

    def set_mode(self, mode=Mode.INFER_MODE):
        if mode in list(Mode):
            old_mode = self.mode
            self.mode = mode
            print(f"Mode changed from {old_mode} to {self.mode}.")  # Update user
    
"""
# Set at start of programs
# Used across functions
dataset_path = ""
dataset_obj = None
dataset_id = None
vars_objs = []
study_design = None

# For variables dictionary
var_name = "name"
var_dtype = "data type"
var_categories = "categories"
var_drange = "range"

# Assumptions
# Stats properties
assumptions = {}
alpha = DEFAULT_ALPHA_PARAMETER

all_results = {}  # Used for multiple comparison correction

# For solver
MODE = "strict"

study_type_determiner = StudyTypeDeterminer()


# For testing purposes
def download_data(url, file_name):
    return load_data_from_url(url, file_name)


def data(file, key=None):
    return Dataset(file)


def define_variables(vars: Dict[str, str]):
    # List of Variables
    variables = []

    for var in vars:
        var_obj = AbstractVariable.create(var)
        variables.append(var_obj)

    return variables


def define_study_design(design: Dict[str, str], variables: list):
    design_obj = AbstractDesign.create(design, variables)

    return design_obj


def assume(assumptions: Dict[str, str], vars_list: list):
    # private function for getting variable by @param name from list of @param variables
    def get_variable(variables: list, name: str):
        # Assume that name is a str
        assert isinstance(name, str)
        for var in variables:
            assert isinstance(var, AbstractVariable)
            if AbstractVariable.get_name(var) == name:
                return var
        return None  # no Variable in the @param variables list has the @param name

    for key, value in assumptions.items():
        if isinstance(value, list):
            for v in value:
                var = get_variable(vars_list, v)
                if var:
                    var.assume(key)
        else:
            var = get_variable(vars_list, value)
            if var:
                var.assume(key)


def set_analysis_mode(mode=INFER_MODE):
    if mode in MODES:
        pass
    else:
        # TODO: More descriptive
        raise ValueError(f"Invalid Mode: Should be one of {MODES}")


def hypothesize(prediction, variables, design, mode=INFER_MODE):
    set_analysis_mode(mode)
    # Create and get back handle to AST node
    relationship = relate(variables, prediction)
    num_comparisons = (
        len(relationship.predictions) if len(relationship.predictions) > 0 else 1
    )  # use for multiple comparison correction

    # Interpret AST node, Returns ResultData object <-- this may need to change
    set_mode(MODE)
    study_type_determiner = StudyTypeDeterminer()
    vardata_factory = VarDataFactory(study_type_determiner)
    result = vardata_factory.create_vardata(dataset_obj, relationship, assumptions, study_design)

    # Make multiple comparison correction
    result.bonferroni_correction(num_comparisons)

    print(f"\n{result}")
    return result


def hypothesize_old(vars: list, prediction: list = None):
    global dataset_path, vars_objs, study_design, dataset_obj, dataset_id
    global assumptions, all_results
    global MODE

    if isinstance(dataset_path, (str, Path)):
        assert dataset_path
    elif isinstance(dataset_path, pd.DataFrame):
        assert not dataset_path.empty
    else:
        raise ValueError(f"dataset_path must be DataFrame, str, or Path. Not: {type(dataset_path)}")
    assert vars_objs
    assert study_design

    dataset_obj = load_data(dataset_path, vars_objs, dataset_id)

    v_objs = []
    for v in vars:
        v_objs.append(get_var_from_list(v, vars_objs))  # may want to use Dataset instance method instead

    # Create and get back handle to AST node
    relationship = relate(v_objs, prediction)
    num_comparisons = (
        len(relationship.predictions) if len(relationship.predictions) > 0 else 1
    )  # use for multiple comparison correction

    # Interpret AST node, Returns ResultData object <-- this may need to change
    set_mode(MODE)
    study_type_determiner = StudyTypeDeterminer()
    vardata_factory = VarDataFactory(study_type_determiner)
    result = vardata_factory.create_vardata(dataset_obj, relationship, assumptions, study_design)

    # Make multiple comparison correction
    result.bonferroni_correction(num_comparisons)

    print(f"\n{result}")
    return result

    # Use assumptions and hypotheses for interpretation/reporting back to user
    # Make result human_readable
    # output = translate(result)

    # Give user output
    # return output


# TODO change how the key is input. Maybe we want to move this to the variables block
def tea_time(data, variables, design, assumptions=None, hypothesis=None, key=None):
    tea_obj = Tea(variables, design, assumptions, hypothesis)
    tea_obj.load_data(data, key)


"""