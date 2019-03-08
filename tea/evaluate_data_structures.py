# Runtime data structures used by interpreter
from .global_vals import *
from .ast import *

import attr
from typing import Any
from types import SimpleNamespace # allows for dot notation access for dictionaries

class Value(object):
    pass

@attr.s(init=True, repr=False, str=False)
class ResultData(Value):
    output = attr.ib(type=str)

    def __repr__(self):
        # Debugging
        pass
    
    def __str__(self):  # Maybe what the user sees?
        # print (ResultData_obj)
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

    def has_explanatory_variable(self): 
        independent_variables = None
        
        if self.get_vars(iv_identifier):
            independent_variables = self.get_vars(iv_identifier)
        elif self.get_vars(contributor_identifier):
            independent_variables  = self.get_vars(contributor_identifier)
        else: 
            pass
            
        return independent_variables

    def has_outcome_variable(self):
        return True

    # Null Hypothesis: Groups come from populations with equal variance
    def has_equal_variance(self): 
        global eq_variance, alpha
        
        if self.properties[eq_variance]: 
            return self.properties[eq_variance][1] >= self.alpha  # Cannot reject null hypothesis of equal variances
        else: 
            return False

    def has_paired_observations(self):
        global paired 

        return self.properties[paired]

    def difference_between_paired_value_is_normal(self):
        if not self.has_paired_observations():
            return False
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