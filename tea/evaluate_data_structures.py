# Runtime data structures used by interpreter

from .ast import *

import attr
from typing import Any
from types import SimpleNamespace # allows for dot notation access for dictionaries

# GLOBAL Property names
data_type = 'dtype'
distribution = 'distribution'
variance = 'variance'

class Value(object):
    pass

@attr.s(init=True)
class VarData(Value):
    # dataframe: Any
    metadata = attr.ib()
    properties = attr.ib(default=None)
    role = attr.ib(default=None)

    def is_normal(self, alpha):
        global distribution
        return self.properties[distribution] >= alpha

    def is_continuous(self): # may want to change this to be is_numeric to be consistent with rest of runtime system?
        global data_type
        return self.metadata[data_type] is DataType.INTERVAL or self.metadata[data_type] is DataType.RATIO
    
    def is_categorical(self): 
        global data_type
        return self.metadata[data_type] is DataType.NOMINAL or self.metadata[data_type] is DataType.ORDINAL
    
    def get_sample_size(self): 
        return len()


@attr.s(init=True, auto_attribs=True)
class CombinedData(Value): # TODO probably want to rename this
    # dataframes: dict # or SimpleNamespace? maybe just a list???
    vars: list # list of VarData objects 
    # set of characteristics about the groups that are used to determine statistical test
    properties: SimpleNamespace
    alpha: attr.ib(default=0.05)

    # TODO add functions that return bools about the properties
    def has_equal_variance(self): 
        global variance
        return self.properties[variance][1] < self.alpha

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