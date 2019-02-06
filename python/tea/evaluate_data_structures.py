# Runtime data structures used by interpreter

from .ast import *

import attr
from typing import Any
from types import SimpleNamespace # allows for dot notation access for dictionaries

class Value(object):
    pass

@attr.s(init=True, auto_attribs=True)
class VarData(Value):
    dataframe: Any
    metadata: Any

@attr.s(init=True, auto_attribs=True)
class CompData(Value): # TODO probably want to rename this
    dataframes: dict # or SimpleNamespace?
    # metadata: SimpleNamespace
    # predictions: Node
    # set of characteristics about the groups that are used to determine statistical test
    properties: SimpleNamespace


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