from typing import Any, Dict, List
from enum import Enum
import unicodedata
import os
import csv
import attr

# class ReadRow(AST):
#     row_num: int
# AST -> Value
# interp("read_row(1)") => Row1

class DataType(Enum): 
    NOMINAL = 'Nominal'
    ORDINAL = 'Ordinal'
    INTERVAL = 'Interval'
    RATIO = 'Ratio'

@attr.s(auto_attribs=True, hash=True)
class DataColumn:
    column: int

    def __iter__(self):
        pass
    
    def __getitem__(self, data, index):
        index = (row_size * row_no + column_no) 
        data_set.data[index]
        

@attr.s(auto_attribs=True, hash=True)
class DataRow:
    # data_set: DataSet
    participant_num: int # Assume each row represents data from one participant
    participant_data: Dict[str, Any] # column_name and value for that column

    def __iter__(self):
        pass

# THIS IS YOUR DSL, EVERYTHING ABOVE ARE SUPPORT STRUCTURES

@attr.s(auto_attribs=True, hash=True)
class Column:
    name: str
    data_type: str
    data: DataColumn

    def __init__(self, data, name, data_type='string'):
        self.name = name
        self.data_type = data_type


    def normal(self):
        pass
    
    def __str__(self) -> str:
        return f"column:{self.name}"

@attr.s(auto_attribs=True, hash=True)
class Row: 
    index: int
    data: DataRow

    def __init__(self, index):
        self.index = index   

class DataSet:
    """
        ds = DataSet.load('...')
        for datum in ds.column(1):
            print(datum)

        sum(ds.column(1)) / len(ds.column(1))
        for col in ds.row(1):
            print(col)
        avg_age = 0.0
        for age in ds.column('age')
            avg_age += arg
        avg_age / len(ds.column('age'))
    """
    # Matrix = [[0 for x in range(w)] for y in range(h)] 
    data: List[Any] # data stored in row-major order
    column_names: List[str]

    def __init__(self, file_path, data_directory='data'):
        self.data  = []
        self.column_names = []

        current_directory = os.getcwd()
        data_file = os.path.join(current_directory, data_directory, file_path)
        with open(data_file, 'r') as readfile:
            reader = csv.reader(readfile, delimiter=',')

            self.column_names = next(reader)
            # for name in column_names:
                # self.column_names += unicodedata.normalize('NFKC', name)
                # self.column_names += name

            for row in reader: 
                self.data += row

    def rows():
        """All rows"""
        pass 

    def cols():
        """All columns"""
        pass

    def column(self, column_number) -> Column:
        pass

    def row(self, row_number) -> Row:
        pass

    # def participant(self, participant_number) -> DataRow:
        # row(self, participant_number)
    
    def __str__(self): 
        return f"Column Names:{self.column_names}"


class Experiment:
    # data: List[Row] # row is like list[string]
    # data: DataSet
    name: str
    file_path: str
    data_set: DataSet

    def __init__(self, name, dataset_file_path) -> None:
        self.name = name
        self.file_path = dataset_file_path
        self.data_set = DataSet(dataset_file_path)

    def column(self, name):
        return self.data_set.get_column(name)
    
    # @staticmethod
    # def experiment(name, file_path):
    #     current_directory = os.getcwd()
    #     data_file = os.path.join(current_directory, data_directory, file_path)

    #     with open(data_file, 'r') as readfile:
    #         reader = csv.reader(readfile)

    #         column_names = next(reader) # first row of the CSV gives the column names
    #         columns = {}
    #         for column in column_names:
    #             columns[column] = Column(column)
                

    #     return Experiment(columns)
    
    def pretty_print(self):
        exp = f"Experiment columns:{self.data_set}"
        
        import pdb; pdb.set_trace()
        return exp
    
    def run(dataset):
        pass


