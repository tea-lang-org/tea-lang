import tisane.variable as tsvars
from tisane.variable import AbstractVariable, AtMost
import tea.build as build
from tea.build import interval, nominal, ordinal, ratio
from .global_vals import *
import typing

class Comparison():    
    def __getitem__(self, item):
        if not hasattr(self, 'items'):
            self.items = list()
        self.items.append(item)
        return self
    
    def __compare_helper(self, other, comparator):
        if hasattr(self, 'items'):
            return str(self.name) + ':' + str(self.items.pop(0)) + comparator  + str(self.items.pop(0))
        else:
            return str(self.name) + comparator + str(other.name)

    def greaterThan(self, other):
        """ Formulates the hypothesis this > other 
        
        Parameters
        ---------------
        other: Tea variable to compare against
        """
        return self.__compare_helper(other, ' > ')

    def lessThan(self, other):
        """ Formulates the hypothesis this < other 
        
        Parameters
        ---------------
        other: Tea variable to compare against
        """
        return self.__compare_helper(other, ' < ')
    
    def linearRelationship(self, other):
        """ Formulates the hypothesis this ~ other. 
        In other words, checks if there exists a linear relationship between this and other 
        
        Parameters
        -------------
        other: Tea variable to compare against
        """
        return self.__compare_helper(other, ' ~ ')
    
    def notEquals(self, other):
        """ Formulates the hypothesis this != other 
        
        Parameters
        ---------------
        other: Tea variable to compare against
        """
        return self.__compare_helper(other, ' != ')
    
    def equals(self, other):
        """ Formulates the hypothesis this = other 
        
        Parameters
        ---------------
        other: Tea variable to compare against
        """
        return self.__compare_helper(other, ' = ')

class Nominal(tsvars.Nominal, Comparison):
    """
        Nominal Tea Variable class. \n
        Nominal variables are described as variables that can be differentiated into finite
        categories but not compared. 

        Parameters
        -------------
        - name: name of the Nominal variable, as found in data
        - categories: list of categories \n
        - data: optional, Data to describe
    """
    def __init__(self, name: str, categories:list, data=None, **kwargs):
        """ Creates a new Nominal variable
        """
        super().__init__(name, data, **kwargs)
        self.categories = categories

class Ordinal(tsvars.Ordinal, Comparison):
    """
        Ordinal Tea Variable class. \n
        Ordinal variables are described as variables that can be differentiated into finite
        comparable categories

        Parameters
        -------------
        - name: name of the ordinal variable, as found in data
        - ordered_categories: list of categories, in ascending order (first category in list is smallest, last category in list is largest)
        - data: optional, Data to describe
    """
    def __init__(self, name: str, ordered_categories: list, cardinality: int = None, data=None):
        """ Creates a new Ordinal variable
        """
        super().__init__(name, ordered_categories, cardinality, data)

class Ratio(tsvars.Numeric, Comparison):
    """
        Ratio Tea Variable class. \n
        Ratio variables describe numeric values

        Parameters
        ---------------
        - name: Name of the ratio variable, as found in data
        - range: optional, range of the described numeric value
        
    """
    def __init__(self, name: str, range: list =None, data=None):
        super().__init__(name, data)
        self.range = range

class Interval(tsvars.Numeric, Comparison):
    """
        Interval Tea Variable class. \n
        Interval variables describe numeric values in a given range

        Parameters
        ---------------
        - name: Name of the interval variable, as found in data
        - range: optional, range of the described numeric value. If not provided, tea will assume the range -infinity to +infinity
    """
    def __init__(self, name: str, range: list =None, data=None):
        super().__init__(name, data)
        self.range = range
        
class Unit(tsvars.Unit):
    """
        Creates a Unit variable

        Parameters
        ---------------
        - name: Name of the unit value, as found in data
        - type: str: Type of unit. One of 'ratio', 'nominal', 'ordinal' or 'interval'.
    """
    def __init__(self, name: str , **kwargs):
        self.name = name
    
    def nominal(
        self, 
        name: str,
        categories: list, 
        **kwargs
    ):
        """
            Creates a nominal variable that is nested inside the specified Unit variable

            Parameters
            --------------
            - name: name of the Nominal variable, as found in data
            - categories: list of categories
            - data: optional, Data to describe
        """
        measure = Nominal(name, categories, data=None, cardinality=None, **kwargs)
        self._has(measure=measure, number_of_instances=None)
        return measure

    def ordinal(
        self,
        name: str,
        ordered_categories: list,
    ):
        """
            Creates an ordinal variale that is nested inside the specified Unit variable

            Parameters
            -------------
            - name: name of the ordinal variable, as found in data
            - ordered_categories: list of categories, in ascending order (first category in list is smallest, last category in list is largest)
            - data: optional, Data to describe

        """
        measure = Ordinal(name=name, ordered_categories=ordered_categories, cardinality=None, data=None)
        # Add relationship to self and to measure
        self._has(measure=measure, number_of_instances=None)
        # Return handle to measure
        return measure
    
    def ratio(
        self,
        name: str,
        range=None,
    ):
        """
        Creates a ratio variable that is nested inside the specified Unit variable

        Parameters
        ---------------
        - name: Name of the ratio variable, as found in data
        - range: optional, range of the described numeric value
        
        """
        # Create new measure
        measure = Ratio(name=name, data=None,range=range)
        # Add relationship to self and to measure
        self._has(measure=measure, number_of_instances=1)
        # Return handle to measure
        return measure
    
    def interval(
        self, 
        name: str, 
        range: list = None, 
    ):
        """
        Creates an interval variable that is nested inside the specified Unit variable

        Parameters
        ---------------
        - name: Name of the interval variable, as found in data
        - range: optional, range of the described numeric value. If not provided, tea will assume the range -infinity to +infinity
        """
        measure = Interval(name=name, range=range)
        return measure



