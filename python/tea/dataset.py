from .ast import Variable, DataType

import attr
import pandas as pd
import os
from typing import Dict

BASE_PATH = os.getcwd()

@attr.s(hash=True)
class Dataset(object): 
    dfile = attr.ib() # path name 
    variables = attr.ib() # list of Variable objects <-- TODO: may not need this in new implementation....
    pid_col_name = attr.ib() # name of column in pandas DataFrame that has participant ids
    row_pids = attr.ib(init=False) # list of unique participant ids
    data = attr.ib(init=False) # pandas DataFrame
    

    def __attrs_post_init__(self): 
        if self.dfile: 
            self.data = pd.read_csv(self.dfile)
            # self.row_pids = self.data[self.pid_col_name] # Change/update based on parameter that is passed to constructor??

        # Reindex DataFrame indices to be pids
        self.data.set_index(self.pid_col_name, inplace=True)

    @classmethod
    def from_arr_numeric(cls, y: list, x: list):

        data = {'X': x, 'Y': y}
        df = pd.DataFrame.from_dict(data)

        x_var = Variable('X', dtype=DataType.INTERVAL, categories=None, drange=None)
        y_var = Variable('Y', dtype=DataType.INTERVAL, categories=None, drange=None)

        return cls(dfile='', variables=[x_var,y_var], data=df)

    
    def __getitem__(self, var_name: str):
        for v in self.variables: # checks that the Variable is known to the Dataset object
            if v.name == var_name: 
                return self.data[var_name] # returns the data, not the variable object

    def get_variable_data(self, var_name: str):
        for v in self.variables: 
            if v.name == var_name:
                return { 'dtype': v.dtype, 
                        'categories': v.categories} 


    # SQL style select
    def select(self, target_var_name: str, where: list):
        # TODO should check that the query is valid (no typos, etc.) before build
        
        def build_query(where: list):
            query = ''

            #build up query based on where clauses 
            for i, e in enumerate(where):
                query += e
                
                if (i+1 < len(where)):
                    query += '&'
            return query

        df = self.data
        query = build_query(where)
        
        import pdb; pdb.set_trace()
        
        res = df.query(query)
        import pdb; pdb.set_trace()



    
    # @param indices are a list of indices for rows that contain the desired data
    def get_subset(self, indices:list):
        pass


# Build SQL like conditions for selecting data
def build_conditions(data, where: Dict[str,str]):
    if not where:
        return
    elif len(where) == 1:
        col, val = where.items()
        return lambda: (data[col] == val)
        # col, val in where.items(): 