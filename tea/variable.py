import tisane.variable as tsvars
from tisane.variable import AbstractVariable, AtMost
import typing

class Unit(tsvars.Unit):
    def __init__(self, name: str, data=None, cardinality: int = None, **kwargs):
        super().__init__(name, data, cardinality, **kwargs)
    
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
    
    # See Tisane code for other variable type definitions


class Nominal(tsvars.Measure):
    def __init__(self, name: str, categories:list, data=None, **kwargs):
        super().__init__(name, data, **kwargs)
        self.categories = categories
    
    def greaterThan(self, other):
        if type(other) is not type(self):
            raise Exception("Nominal variable must be compared to another nominal variable")
        assert(self.data is not None)



