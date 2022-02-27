import tisane.variable as tsvars
from tisane.variable import AbstractVariable, AtMost
from tea.api import vars_objs
from tea.build import nominal, ordinal, ratio
from .global_vals import *
import typing

'''
TODO: Add realtion operators to every type. For hypothesize new syntax. 
'''

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


class Nominal(tsvars.Nominal):
    def __init__(self, name: str, categories:list, data=None, **kwargs):
        super().__init__(name, data, **kwargs)
        self.categories = categories
        vars_objs.append(nominal(name, categories))
    
    def greaterThan(self, other):
        if type(other) is not type(self):
            raise Exception("Nominal variable must be compared to another nominal variable")
        assert(self.data is not None)

class Ordinal(tsvars.Ordinal):
    def __init__(self, name: str, order: list, cardinality: int = None, data=None):
        super().__init__(name, order, cardinality, data)
        vars_objs.append(ordinal(name, order))

class Numeric(tsvars.Numeric):
    def __init__(self, name: str, data=None, range=None):
        super().__init__(name, data)
        self.range = range
        vars_objs.append(ratio(name, range))




