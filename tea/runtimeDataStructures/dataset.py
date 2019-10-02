import attr
import pandas as pd
import os
import csv
from typing import Dict
from pathlib import Path
from urllib.parse import urlparse
import requests

from .variables import (ordinal, isordinal,
                    nominal, isnominal,
                    ratio, isratio,
                    interval, isinterval
                   )

BASE_PATH = os.getcwd()

def _dir_exists(path):
    return os.path.isdir(path) and os.path.exists(path)

@attr.s(hash=True)
class Dataset(object): 
    dfile = attr.ib(default=None,kw_only=True) # path name 
    variables = attr.ib(init=False) # list of Variable objects <-- TODO: may not need this in new implementation....
    pid_col_name = attr.ib(default=None,kw_only=True) # name of column in pandas DataFrame that has participant ids
    row_pids = attr.ib(init=False) # list of unique participant ids
    data = attr.ib(init=False) # pandas DataFrame
    
    @staticmethod
    def load_url(path: str, name):
        assert(isinstance(path, str))
        home = Path.home()
        tea_path = home / '.tea'
        if not _dir_exists(tea_path):
            os.mkdir(tea_path)
        data_path = tea_path / 'data'
        if not _dir_exists(data_path):
            os.mkdir(data_path)
        
        url = urlparse(path)
        csv_name = name if '.csv' in name else str(name + '.csv')
        csv_path = data_path / csv_name

        # URL
        if url.scheme != '':
            data = requests.get(path)

            with open(csv_path, 'w') as f:
                writer = csv.writer(f)
                reader = csv.reader(data.text.splitlines())

                for row in reader:
                    writer.writerow(row)
        else: 
            with open(path, 'r') as readfile: 
                reader = csv.reader(readfile)
                with open(csv_path, 'w') as writefile:
                    writer = csv.writer(writefile)

                    for row in reader:
                        writer.writerow(row)

        return csv_path

    def load_df(self, df: pd.DataFrame):
        self.data = df

    def __attrs_post_init__(self): 
        if self.dfile: 
            self.data = pd.read_csv(self.dfile)

        # if self.pid_col_name:
        #     # Reindex DataFrame indices to be pids
        #     self.data.set_index(self.pid_col_name, inplace=True)
        # else: 
            # Treat each row as a unique observation

    
    def __getitem__(self, var_name: str):
        for v in self.variables: # checks that the Variable is known to the Dataset object
            if v.name == var_name: 
                return self.data[var_name] # returns the data, not the variable object

    def set_variables(self, vars: Dict[str, str]):
        var_dtype = 'data type'
        var_name = 'name'
        var_dtype = 'data type'
        var_categories = 'categories'
        var_drange = 'range'
        self.variables = []

        for var in vars: 
            name = var['name']

            if (var[var_dtype] == 'nominal'): 
                categories = var[var_categories]
                v_obj = nominal(name, categories)
            elif (var[var_dtype] == 'ordinal'): 
                categories = var[var_categories]
                v_obj = ordinal(name, categories)
            elif (var[var_dtype] == 'interval'): 
                drange=None
                if var_drange in var: 
                    drange = var[var_drange]
                v_obj = interval(name, drange)
            else: 
                assert(var[var_dtype] == 'ratio')
                drange = var[var_drange] if var_drange in var else None
                v_obj = interval(name, drange)

            self.variables.append(v_obj)

    # Returns variable object -- may want to altogether replace the __getitem__
    def get_variable(self, var_name: str): 
        for v in self.variables: 
            if v.name == var_name: 
                return v

    def get_variable_data(self, var_name: str):
        for v in self.variables: 
            if v.name == var_name:
                return { 'dtype': v.dtype, 
                        'categories': v.categories} 


    # SQL style select
    def select(self, col: str, where: list = None):
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
        if where: # not None
            query = build_query(where)
            res = df.query(query)[col] # makes a copy
        else: 
            res = df[col]

        return res