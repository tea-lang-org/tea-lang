import tisane.variable as tsvars
from tisane.variable import AbstractVariable, AtMost
from tea.api import vars_objs
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
        return self.__compare_helper(other, ' > ')

    def lessThan(self, other):
        return self.__compare_helper(other, ' < ')
    
    def linearRelationship(self, other):
        return self.__compare_helper(other, ' ~ ')
    
    def notEquals(self, other):
        return self.__compare_helper(other, ' != ')
    
    def equals(self, other):
        return self.__compare_helper(other, ' = ')

class Nominal(tsvars.Nominal, Comparison):
    def __init__(self, name: str, categories:list, data=None, **kwargs):
        super().__init__(name, data, **kwargs)
        self.categories = categories
        vars_objs.append(nominal(name, categories))

class Ordinal(tsvars.Ordinal, Comparison):
    def __init__(self, name: str, ordered_categories: list, cardinality: int = None, data=None):
        super().__init__(name, ordered_categories, cardinality, data)
        vars_objs.append(ordinal(name, ordered_categories))

class Numeric(tsvars.Numeric, Comparison):
    def __init__(self, name: str, range: list =None, data=None):
        super().__init__(name, data)
        self.range = range
        vars_objs.append(ratio(name, range))

class Interval(Comparison):
    def __init__(self, name: str, range: list = None):
        self.name = name
        self.range = range
        vars_objs.append(interval(name, range))
        
class Unit(tsvars.Unit):
    def __init__(self, name: str, data=None, cardinality: int = None, **kwargs):
        super().__init__(name, data, cardinality, **kwargs)
        v_obj = ratio(name, None)
        vars_objs.append(v_obj)
    
    def nominal(
        self, 
        name: str,
        categories: list, 
        **kwargs
    ):
        measure = Nominal(name, categories, data=None, cardinality=None, **kwargs)
        self._has(measure=measure, number_of_instances=None)
        return measure

    def ordinal(
        self,
        name: str,
        ordered_categories: list,
    ):
        measure = Ordinal(name=name, ordered_categories=ordered_categories, cardinality=None, data=None)
        # Add relationship to self and to measure
        self._has(measure=measure, number_of_instances=None)
        # Return handle to measure
        return measure
    
    def numeric(
        self,
        name: str,
        range=None,
    ):
        # Create new measure
        measure = Numeric(name=name, data=None,range=range)
        # Add relationship to self and to measure
        self._has(measure=measure, number_of_instances=1)
        # Return handle to measure
        return measure
    
    def interval(
        self, 
        name: str, 
        range: list = None, 
    ):
        # Create new "Measure", interval is not really a measure FYI
        # Measure is a class in Tisane, and tisane does not have "interval" type
        measure = Interval(name=name, range=range)
        # Add relationship to self and to measure
        # TODO: Do I add interval to Tisane???? 
        # Return handle to measure
        return measure



