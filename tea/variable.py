import tisane.variable as tsvars
from tisane.variable import AbstractVariable, AtMost
from tea.api import vars_objs
from tea.build import nominal, ordinal, ratio
from .global_vals import *
import typing

class Comparison():    
    def __getitem__(self, item):
        if not hasattr(self, 'items'):
            self.items = list()
        self.items.append(item)
        return self
    
    def __compare_helper(self, other, comparator):
        assert type(self) == type(other)
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

class Nominal(tsvars.Nominal, Comparison):
    def __init__(self, name: str, categories:list, data=None, **kwargs):
        super().__init__(name, data, **kwargs)
        self.categories = categories
        vars_objs.append(nominal(name, categories))

class Ordinal(tsvars.Ordinal, Comparison):
    def __init__(self, name: str, order: list, cardinality: int = None, data=None):
        super().__init__(name, order, cardinality, data)
        vars_objs.append(ordinal(name, order))

class Numeric(tsvars.Numeric, Comparison):
    def __init__(self, name: str, data=None, range=None):
        super().__init__(name, data)
        self.range = range
        vars_objs.append(ratio(name, range))
        
class Unit(tsvars.Unit):
    def __init__(self, name: str, data=None, cardinality: int = None, **kwargs):
        super().__init__(name, data, cardinality, **kwargs)
        v_obj = ratio(name, None)
        vars_objs.append(v_obj)
    
    def nominal(
        self, 
        name: str,
        categories: list, 
        data=None, 
        cardinality=None, 
        number_of_instances: typing.Union[int, AbstractVariable, "AtMost"] = 1, 
        **kwargs
    ):
        measure = Nominal(name, categories, data=data, cardinality=cardinality, **kwargs)
        self._has(measure=measure, number_of_instances=number_of_instances)
        return measure

    def ordinal(
        self,
        name: str,
        order: list,
        cardinality: int = None,
        data=None,
        number_of_instances: typing.Union[int, AbstractVariable, "AtMost"] = 1,
    ):
        measure = Ordinal(name=name, order=order, cardinality=cardinality, data=data)
        # Add relationship to self and to measure
        self._has(measure=measure, number_of_instances=number_of_instances)
        # Return handle to measure
        return measure
    
    def numeric(
        self,
        name: str,
        data=None,
        number_of_instances: typing.Union[int, AbstractVariable, "AtMost"] = 1,
    ):
        # Create new measure
        measure = Numeric(name=name, data=data)
        # Add relationship to self and to measure
        self._has(measure=measure, number_of_instances=number_of_instances)
        # Return handle to measure
        return measure
