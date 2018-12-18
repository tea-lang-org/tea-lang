import attr
import pandas as pd
import os

BASE_PATH = os.getcwd()

@attr.s(init=False)
class Dataset(object): 
    # variables: list
    # variable_names: list
    # data: list

    def __init__(self, data=None, variable_names=None, variables=None): 
        self.variables = None
        self.variable_names = None
        self.data = None

    def load_data(self, source_name):
        source_path = BASE_PATH + '/Datasets/' + source_name
        data = pd.read_csv(source_path)

        # Check that each column has a unique variable name
        variable_names = data.columns.values.tolist()

        # There are duplicates
        if (len(variable_names) != len(set(variable_names))):
            seen = set()
            duplicates = dict()
            for v in variable_names:
                if v not in seen:
                    seen.add(v)
                else:  #already seen
                    duplicates.append(v)
                    dup_counts.append(1)
                
            # TODO: Raise error here for duplicates!
            raise Exception('Duplictes! - may want to pass to pretty print warning/error')

            duplicates = []
        else:  # Only assign data to dataset if there are not variable name collisions
            self.data = data
            self.variable_names = variable_names
            self.variables = list()
    
    def initialize_variables(self, order): 
        pass
    
    def set_variable(self, var_name, var_type, var_categories=None): 
        # assert(var_name in self.variable_names)
        var = Variable(var_name, var_type, var_categories)
        self.variables.append(var)

    def get_variable(self, var_name): 
        assert(var_name in self.variable_names)
        
        var_data = self.data[var_name]
        idx = [i for i,v in enumerate(self.variables) if (v.name == var_name)].pop()
        var_type = self.variables[idx].data_type

        if (var_type == DataType.INTERVAL or var_type == DataType.RATIO): 
            var_data = pd.to_numeric(var_data)
        else: 
            var_data = [str(d) for i,d in enumerate(var_data)]
        return (self.variables[idx], var_data)