import attr
from typing import Dict

from tea.global_vals import *
from tea.runtimeDataStructures.variable import AbstractVariable, NominalVariable, OrdinalVariable, NumericVariable


class AbstractDesign(object):
    xs : list # list of Variables
    ys : list # list of Variables
    
    @classmethod
    def create(cls, attributes, variables):
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

    def which_role(self, variable):
        if self.has_x(variable):
            return 'X'
        elif self.has_y(variable):
            return 'Y'
        else: 
            raise ValueError(f"Variable {AbstractVariable.get_name(variable)} does not have a role in this design: {self}")

    def has_x(self, variable): 
        return variable in self.xs
    
    def has_y(self, variable): 
        return variable in self.ys

@attr.s(init=False)
class ObservationalDesign(AbstractDesign): 

    def __init__(self, attributes, variables): 

        for key, value in attributes.items():
            if key in OBS_X: 
                # Assign observational x variable, must be a list first
                if isinstance(value, list): 
                    self.xs = [AbstractVariable.get_variable(variables, v) for v in value]
                    # TODO make sure to get the variable from the variables list, assign Variable object
                elif isinstance(value, str): 
                    self.xs = [AbstractVariable.get_variable(variables, value)]
                else: 
                    raise ValueError(f"{value} for {key} is neither a list nor a string.")
            elif key in OBS_Y: 
                if isinstance(value, list): 
                    self.ys = [AbstractVariable.get_variable(variables, v) for v in value]
                elif isinstance(value, str): 
                    self.ys = [AbstractVariable.get_variable(variables, value)]
                else: 
                    raise ValueError(f"{value} for {key} is neither a list nor a string.")
            elif key == STUDY_TYPE: 
                pass # already handled to AbstractDesign
            elif key in EXP_X: 
                raise ValueError(f"{key} is not available in an {OBS_STUDY}. Did you mean to say the study is an {EXPERIMENT} or that the variable/s are one of {OBS_X}?")
            elif key in EXP_Y: 
                raise ValueError(f"{key} is not available in an {OBS_STUDY}. Did you mean to say the study is an {EXPERIMENT} or that the variable/s are one of {OBS_Y}?")
            else: 
                print(f"Extra aspects of study design are not necessary and not considered:{key}, {value}")
            
@attr.s(init=False)
class ExperimentDesign(AbstractDesign):
    
    def __init__(self, attributes, variables): 
    
        for key, value in attributes.items():
            if key in EXP_X: 
                # Assign observational x variable, must be a list first
                if isinstance(value, list): 
                    self.xs = [AbstractVariable.get_variable(variables, v) for v in value]
                    # TODO make sure to get the variable from the variables list, assign Variable object
                elif isinstance(value, str): 
                    self.xs = [AbstractVariable.get_variable(variables, value)]
                else: 
                    raise ValueError(f"{value} for {key} is neither a list nor a string.")
            elif key in EXP_Y: 
                if isinstance(value, list): 
                    self.ys = [AbstractVariable.get_variable(variables, v) for v in value]
                elif isinstance(value, str): 
                    self.ys = [AbstractVariable.get_variable(variables, value)]
                else: 
                    raise ValueError(f"{value} for {key} is neither a list nor a string.")
            elif key == STUDY_TYPE: 
                pass # already handled to AbstractDesign
            elif key in OBS_X: 
                raise ValueError(f"{key} is not available in an {EXPERIMENT}. Did you mean to say the study is an {OBS_STUDY} or that the variable/s are one of {EXP_X}?")
            elif key in OBS_Y: 
                raise ValueError(f"{key} is not available in an {EXPERIMENT}. Did you mean to say the study is an {OBS_STUDY} or that the variable/s are one of {EXP_Y}?")
            else: 
                print(f"Extra aspects of study design are not necessary and not considered:{key}, {value}")

    # TODO Do we want this?
    def __eq__(self, other): 
        if len(self.xs) == len(other.xs):
            if len(self.ys) == len(other.ys):
                xs_found = [x in other.xs for x in self.xs]
                ys_found = [y in other.ys for y in self.ys]

                return all(xs_found) and all(ys_found)
                    
        return False
    


 




  