# Runtime data structures used by interpreter

from .ast import *

import attr
from typing import Any
from types import SimpleNamespace # allows for dot notation access for dictionaries

## TODO Store keys here
#global variance_key = 'variance'
# properties[variance_key]

class Value(object):
    pass

@attr.s(init=True)
class VarData(Value):
    # dataframe: Any
    metadata = attr.ib()
    properties = attr.ib(default=None)
    role = attr.ib(default=None)

@attr.s(init=True, auto_attribs=True)
class CombinedData(Value): # TODO probably want to rename this
    # dataframes: dict # or SimpleNamespace? maybe just a list???
    vars: list # list of VarData objects 

    # set of characteristics about the groups that are used to determine statistical test
    properties: SimpleNamespace

    def is_normal(self, alpha):
        reutrn self.properties[distribution] < alpha 

    # TODO add functions that return bools about the properties

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