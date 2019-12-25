## Abstract Factory pattern to create Variables
# TODO: Probably want to make Variable a combination of VarData and MultivariateData? 
import attr
from abc import abstractmethod

from tea.global_vals import *

class AbstractVariable(object):
    
    @classmethod
    def create(cls, attributes):
        if VARIABLE_TYPE in attributes.keys(): 
            var_type = attributes[VARIABLE_TYPE]
            if var_type == NOMINAL: 
                return NominalVariable(attributes)
            elif var_type == ORDINAL: 
                return OrdinalVariable(attributes)
            elif var_type == NUMERIC: 
                return NumericVariable(attributes)
            elif var_type == INTERVAL:
                return NumericVariable(attributes)
            elif var_type == RATIO: 
                return NumericVariable(attributes)
            else: 
                raise ValueError(f"Type of variable is not supported: {var_type}")
        else: 
            raise ValueError(f"Missing type information for variable {attributes[VARIABLE_NAME]}! Type can be {NOMINAL}, {ORDINAL}, {NUMERIC} ({INTERVAL} or {RATIO}).")

    @staticmethod
    def get_name(var):
        return  var.name

    @classmethod
    def get_variable(cls, variables: list, name: str):  
            # Assume that name is a str
            assert(isinstance(name, str))
            for var in variables: 
                assert(isinstance(var, AbstractVariable))
                if AbstractVariable.get_name(var) == name: 
                    return var
            return None #no Variable in the @param variables list has the @param name
    
    @abstractmethod
    def assume(self, prop):
        pass

@attr.s(init=False)
class NominalVariable(AbstractVariable): 
    name: str
    categories: list
    properties: list

    def __init__(self, attributes): 
        for key, value in attributes.items(): 
            if key == VARIABLE_NAME: 
                self.name = value
            elif key == VARIABLE_CATEGORIES: 
                self.categories = value
            elif key == VARIABLE_TYPE: 
                pass # already handled in AbstractVariable
            else:
                print(f"Extra attribute not necessary for nominal variable:{key}, {value}")
        
        if not hasattr(self, categories):
            self.extract_categories()
        self.properties = [] # empty list of properties that are assumed/validated

    def extract_categories(self): 
        self.categories = None

    def assume(self, prop):
        if prop in NOMINAL_DATA_PROPS: 
            self.properties.append(prop)
        else: 
            raise ValueError(f"{prop} is not a data property that is supported. Did you mean one of {NOMINAL_DATA_PROPS}?")

@attr.s(init=False)
class OrdinalVariable(AbstractVariable): 
    name: str
    categories: list
    properties: list

    def __init__(self, attributes): 
        for key, value in attributes.items(): 
            if key == VARIABLE_NAME: 
                self.name = value
            elif key == VARIABLE_CATEGORIES: 
                self.categories = value
            elif key == VARIABLE_TYPE: 
                pass # already handled to AbstractVariable
            else:
                print(f"Extra attribute not necessary for ordinal variable:{key}, {value}")
        
        assert(self.categories) # Cannot extract categories with ordinal data. Need to have user provide order
        
        self.properties = [] # empty list of properties that are assumed/validated

    def assume(self, prop):
        if prop in ORDINAL_DATA_PROPS: 
            self.properties.append(prop)
        else: 
            raise ValueError(f"{prop} is not a data property that is supported. Did you mean one of {ORDINAL_DATA_PROPS}?")

@attr.s(init=False)
class NumericVariable(AbstractVariable): 
    name: str
    properties: list

    def __init__(self, attributes): 
        for key, value in attributes.items(): 
            if key == VARIABLE_NAME: 
                self.name = value
            elif key == VARIABLE_TYPE: 
                pass # already handled to AbstractVariable
            else:
                print(f"Extra attribute not necessary for numeric variable:{key}, {value}")
        
        self.properties = [] # empty list of properties that are assumed/validated
    
    def assume(self, prop):
        if prop in NUMERIC_DATA_PROPS: 
            self.properties.append(prop)
        else: 
            raise ValueError(f"{prop} is not a data property that is supported. Did you mean one of {NUMERIC_DATA_PROPS}?")