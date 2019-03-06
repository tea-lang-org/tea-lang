# Runtime data structures used by interpreter

from .ast import *

import attr
from typing import Any
from types import SimpleNamespace # allows for dot notation access for dictionaries

# GLOBAL Property names
data_type = 'dtype'
distribution = 'distribution'
variance = 'variance'
sample_size = 'sample size'
num_categories = 'number of categories'

class Value(object):
    pass

@attr.s(init=True)
class VarData(Value):
    # dataframe: Any
    metadata = attr.ib()
    properties = attr.ib(default=dict())
    role = attr.ib(default=None)

    def is_normal(self, alpha):
        global distribution
        return self.properties[distribution][1] >= alpha

    def is_continuous(self): # may want to change this to be is_numeric to be consistent with rest of runtime system?
        global data_type
        return self.metadata[data_type] is DataType.INTERVAL or self.metadata[data_type] is DataType.RATIO
    
    def is_categorical(self): 
        global data_type
        return self.metadata[data_type] is DataType.NOMINAL or self.metadata[data_type] is DataType.ORDINAL

    def is_ordinal(self):
        global data_type
        return self.metadata[data_type] is DataType.ORDINAL
    
    def get_sample_size(self): 
        return self.properties[sample_size]
    
    def get_number_categories(self): 
        if num_categories in self.properties: 
            return self.properties[num_categories]


@attr.s(init=True)
class CombinedData(Value): # TODO probably want to rename this
    vars = attr.ib(default=[]) # list of VarData objects 
    # set of characteristics about the groups that are used to determine statistical test
    properties = attr.ib(default=dict())
    alpha = attr.ib(type=float, default=0.05)

    # TODO add functions that return bools about the properties
    def has_equal_variance(self): 
        global variance
        return self.properties[variance][1] < self.alpha

    def has_paired_observations(self):
        assert False, "Implement this property to convey information about whether observations are paired."

    def difference_between_paired_value_is_normal(self):
        assert self.has_paired_observations(), "This method only makes sense when observations are paired."
        assert False, "Implement this property to convey information about whether difference" \
                      "between paired values is normally distributed."
    
    # @return list of VarData instances that are in this object's vars that have the @param role
    def get_vars(self, role: str): 
        role_vars = []
        for v in self.vars:
            if v.role == role: 
                role_vars.append(v) 
        
        return role_vars

@attr.s(init=True, auto_attribs=True)
class BivariateData(CombinedData):
    pass

@attr.s(init=True, auto_attribs=True)
class MultivariateData(CombinedData):
    pass

@attr.s(init=True, auto_attribs=True, str=False)
class ResData(Value):
    iv: str # Name of IV
    dv: str # Name of DV
    test_name: str 
    results: Any
    properties: Any
    predictions: Any
    

    def __str__(self):
        summary = f"Compared {self.dv} as dependent variables between independent variables: {self.iv}"
        test = f"\nConducted {self.test_name}: test statistic: {self.results[0]}, p-value: {self.results[1]}"
        reason = f"\nBecause of these properties of the data: {self.properties}"

        return summary + test + reason