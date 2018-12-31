from .ast import Variable, DataType

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
        if self.dfile: 
            self.data = pd.read_csv(self.dfile)
        # TODO Check that there are duplicates? 
        # self.variable_names = self.data.columns.values.tolist()

    @classmethod
    def from_arr_numeric(cls, y: list, x: list):

        data = {'X': x, 'Y': y}
        df = pd.DataFrame.from_dict(data)

        x_var = Variable('X', dtype=DataType.INTERVAL, categories=None, drange=None)
        y_var = Variable('Y', dtype=DataType.INTERVAL, categories=None, drange=None)

        return cls(dfile='', variables=[x_var,y_var], data=df)

    def get_data(self, var: Variable): 
        var_data = self.data[var.name]

        if (var.dtype == DataType.INTERVAL or var.dtype == DataType.RATIO): 
            return pd.to_numeric(var_data)
        else:
            return [str(d) for i,d in enumerate(var_data)]
    
    # FOR TESTING
    def get_variable(self, var_name: str): 
        for v in self.variables: 
            if v.name == var_name: 
                return v

    # def get_variable(self, var): 
    #     # assert(var_name in self.variable_names)
        
    #     var_data = self.data[var.name]
    #     idx = [i for i,v in enumerate(self.variables) if (v.name == var.name)].pop()
    #     var_type = self.variables[idx].data_type

    #     if (var_type == DataType.INTERVAL or var_type == DataType.RATIO): 
    #         var_data = pd.to_numeric(var_data)
    #     else: 
    #         var_data = [str(d) for i,d in enumerate(var_data)]
    #     return (self.variables[idx], var_data)