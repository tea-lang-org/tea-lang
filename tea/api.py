from tea.logging.tea_logger import TeaLogger
from tea.helpers.study_type_determiner import StudyTypeDeterminer
import pandas as pd

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

from tea.runtimeDataStructures.dataset import Dataset
from tea.runtimeDataStructures.variable import AbstractVariable, NominalVariable, OrdinalVariable, NumericVariable
from tea.runtimeDataStructures.design import AbstractDesign, ObservationalDesign, ExperimentDesign

from typing import Dict
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
assumptions = {}
alpha = DEFAULT_ALPHA_PARAMETER

all_results = {}  # Used for multiple comparison correction

# For solver
MODE = 'strict'

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
        assert(isinstance(name, str))
        for var in variables: 
            assert(isinstance(var, AbstractVariable))
            if AbstractVariable.get_name(var) == name: 
                return var
        return None # no Variable in the @param variables list has the @param name

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

def set_mode(mode=INFER_MODE): 
    if mode in MODES: 
        pass
    else: 
        #TODO: More descriptive
        raise ValueError(f"Invalid Mode: Should be one of {MODES}")

def hypothesize(variables, design, assumptions, mode=None): 
    pass    

def hypothesize_old(vars: list, prediction: list = None):
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


# TODO: This is a wrapper around the other API calls.
# Public facing Tea object end-user can construct 
class Tea(object): 
    data: None
    mode: str
    variables: list
    design: AbstractDesign
    # hypothesis: str

    def __init__(self, variables: Dict[str, str], design: Dict[str, str], assumptions=None, hypothesis=None): 
        self.variables = self.define_variables(variables)
        self.design = self.define_study_design(design, self.variables)
        self.mode = INFER_MODE

    def set_mode(mode=INFER_MODE): 
        if mode in MODES: 
            pass
        else: 
            #TODO: More descriptive
            raise ValueError(f"Invalid Mode: Should be one of {MODES}")

    def load_data(self, file, key=None): 
        self.data = Dataset(file)

        return self.data

    def define_variables(self, vars: Dict[str, str]): 
        # List of Variables 
        variables = []

        for var in vars: 
            var_obj = AbstractVariable.create(var)
            variables.append(var_obj)
        
        return variables
    
    def define_study_design(self, design: Dict[str, str], variables: list): 
        design_obj = AbstractDesign.create(design, variables)
    
        return design_obj

    def assume(self, assumptions: Dict[str, str]): 
        vars_list = self.variables
        # private function for getting variable by @param name from list of @param variables
        def get_variable(variables: list, name: str):  
            # Assume that name is a str
            assert(isinstance(name, str))
            for var in variables: 
                assert(isinstance(var, AbstractVariable))
                if AbstractVariable.get_name(var) == name: 
                    return var
            return None # no Variable in the @param variables list has the @param name

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

    def hypothesize(self, hypothesis): 
        pass