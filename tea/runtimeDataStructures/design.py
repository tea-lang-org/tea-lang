from typing import Dict

from tea.global_vals import *
from tea.runtimeDataStructures.variable import AbstractVariable, NominalVariable, OrdinalVariable, NumericVariable


class AbstractDesign(object):
    
    @staticmethod
    def create(attributes, variables):
        if STUDY_TYPE in attributes: 
            study = attributes[STUDY_TYPE]
            if study == OBS_STUDY: 
                return ObservationalDesign(attributes, variables)
            elif study == EXPERIMENT: 
                return ExperimentDesign(attributes, variables)
            else:
                raise ValueError(f"Study type is not supported: {study}. Study can be {OBS_STUDY} or {EXPERIMENT}.")
        else: 
            raise ValueError(f"Missing study type information! Study can be {OBS_STUDY} or {EXPERIMENT}.")

class ObservationalDesign(AbstractDesign): 
    xs : list # list of Variables
    ys : list # list of Variables

    def __init__(self, attributes, variables): 
        # private function for getting variable by @param name from list of @param variables
        def get_variable(variables: list, name: str):  
            # Assume that name is a str
            assert(isinstance(name, str))
            for var in variables: 
                assert(isinstance(var, AbstractVariable))
                if AbstractVariable.get_name(var) == name: 
                    return var

        for key, value in attributes.items():
            if key in OBS_X: 
                # Assign observational x variable, must be a list first
                if isinstance(value, list): 
                    self.xs = [get_variable(variables, v) for v in value]
                    # TODO make sure to get the variable from the variables list, assign Variable object
                elif isinstance(value, str): 
                    self.xs = [get_variable(variables, value)]
                else: 
                    raise ValueError(f"{value} for {key} is neither a list nor a string.")
            elif key in OBS_Y: 
                if isinstance(value, list): 
                    self.ys = [get_variable(variables, v) for v in value]
                elif isinstance(value, str): 
                    self.ys = [get_variable(variables, value)]
                else: 
                    raise ValueError(f"{value} for {key} is neither a list nor a string.")
            else: 
                print(f"Extra aspects of study design are not necessary and not considered:{key}, {value}")
            

class ExperimentDesign(AbstractDesign):
    
    def __init(self, attributes): 
        pass


 




  