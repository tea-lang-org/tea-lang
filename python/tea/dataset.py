import attr
import pandas as pd
import os

BASE_PATH = os.getcwd()

@attr.s
class Dataset(object): 
    dfile = attr.ib()
    variables = attr.ib()
    # variabe_names = attr.ib(init=False)
    data = attr.ib(init=False)

    def __attrs_post_init__(self): 
        self.data = pd.read_csv(self.dfile)
        # TODO Check that there are duplicates? 
        # self.variable_names = self.data.columns.values.tolist()

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