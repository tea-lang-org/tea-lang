import attr
import pandas as pd
import os
import csv
from pathlib import Path
from urllib.parse import urlparse
import requests

BASE_PATH = os.getcwd()


def _dir_exists(path):
    return os.path.isdir(path) and os.path.exists(path)


@attr.s(hash=True)
class Dataset(object): 
    dfile = attr.ib()  # path name
    variables = attr.ib()  # list of Variable objects <-- TODO: may not need this in new implementation....
    pid_col_name = attr.ib()  # name of column in pandas DataFrame that has participant ids
    row_pids = attr.ib(init=False)  # list of unique participant ids
    data = attr.ib(init=False)  # pandas DataFrame
    
    @staticmethod
    def load(path: str, name):
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

    def __attrs_post_init__(self):
        if isinstance(self.dfile, (str, Path)):
            self.data = pd.read_csv(self.dfile)
        elif isinstance(self.dfile, pd.DataFrame):
            self.data = self.dfile
        else:
            raise ValueError(f"Dataset expected DataFrame, str, or Path. Received: {self.dfile}")

        # if self.pid_col_name:
        #     # Reindex DataFrame indices to be pids
        #     self.data.set_index(self.pid_col_name, inplace=True)
        # else: 
            # Treat each row as a unique observation

    def __getitem__(self, var_name: str):
        for v in self.variables:  # checks that the Variable is known to the Dataset object
            if v.name == var_name: 
                return self.data[var_name]  # returns the data, not the variable object

    # Returns variable object -- may want to altogether replace the __getitem__
    def get_variable(self, var_name: str): 
        for v in self.variables: 
            if v.name == var_name: 
                return v

    def get_variable_data(self, var_name: str):
        for v in self.variables: 
            if v.name == var_name:
                return {'dtype': v.dtype,
                        'categories': v.categories} 

    # SQL style select
    def select(self, col: str, where: list = None):
        # TODO should check that the query is valid (no typos, etc.) before build

        def build_query(where: list):
            query = ''

            # build up query based on where clauses
            for i, e in enumerate(where):
                query += e
                
                if i+1 < len(where):
                    query += '&'
            return query

        df = self.data
        if where: # not None
            query = build_query(where)
            res = df.query(query)[col] # makes a copy
        else: 
            res = df[col]

        return res