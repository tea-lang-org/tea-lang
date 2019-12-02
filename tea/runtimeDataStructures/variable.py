## Abstract Factory pattern to create Variables
# TODO: Probably want to make Variable a combination of VarData and MultivariateData? 
import attr

from tea.global_vals import *

class AbstractVariable(object):
    
    @staticmethod
    def create(attributes):
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

@attr.s(init=False)
class NominalVariable(AbstractVariable): 
    name: str
    categories: list

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

    def extract_categories(self): 
        self.categories = None

@attr.s(init=False)
class OrdinalVariable(AbstractVariable): 
    name: str
    categories: list

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

@attr.s(init=False)
class NumericVariable(AbstractVariable): 
    name: str

    def __init__(self, attributes): 
        for key, value in attributes.items(): 
            if key == VARIABLE_NAME: 
                self.name = value
            elif key == VARIABLE_TYPE: 
                pass # already handled to AbstractVariable
            else:
                print(f"Extra attribute not necessary for numeric variable:{key}, {value}")
