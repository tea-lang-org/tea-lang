from tea.global_vals import *
from tea.helpers.constants.default_values import DEFAULT_ALPHA_PARAMETER
from .value import Value
from tea.ast import DataType

import attr


@attr.s(init=True)
class VarData(Value):
    # dataframe: Any
    metadata = attr.ib()
    properties = attr.ib(default=dict())
    role = attr.ib(default=None)

    def is_normal(self, alpha=DEFAULT_ALPHA_PARAMETER):
        global normal_distribution

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

    def get_name(self): 
        assert(self.metadata) # metadata is not empty
        return self.metadata['var_name'] # hardcoded, my want to change this in the future
        