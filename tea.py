from typing import Any, Dict
import os
import csv
import attr

# class ReadRow(AST):
#     row_num: int
# AST -> Value
# interp("read_row(1)") => Row1


class DataColumn:
    def __iter__(self):
        pass

class DataRow:
    def __iter__(self):
        pass


class DataStore:
    """
        ds = DataStore.load('...')
        for datum in ds.column(1):
            print(datum)

        sum(ds.column(1)) / len(ds.column(1))
        for col in ds.row(1):
            print(col)
    """
    data: List[string]
    column_index: ...
    row_index: ...

    def rows():
        """All rows"""
        pass 

    def cols():
        """All columns"""
        pass

    def column(self, column_number) -> DataColumn:
        pass

    def row(self, row_number) -> DataRow:
        pass

@attr.s(auto_attribs=True, hash=True)
class Column:
    name: str
    data_type: str
    data: DataColumn

    def __init__(self, name, data_type='string'):
        self.name = name
        self.data_type = data_type

    def normal(self):
        pass
    
    # def __str__(self) -> str:
    #     return f"column:{name}"

class Experiment:
    data: List[Row] # row is like list[string]
    data: 
    columns: Dict[str, Column]

    def __init__(self, columns) -> None:
        self.data = None
        self.columns = columns
    
    def column(self, name):
        return self.columns[name]
    
    @staticmethod
    def load(name, file_path, data_directory='data'):
        current_directory = os.getcwd()
        data_file = os.path.join(current_directory, data_directory, file_path)
        with open(data_file, 'r') as readfile:
            reader = csv.reader(readfile)

            column_names = next(reader)
            columns = {}
            for column in column_names:
                columns[column] = Column(column)

        return Experiment(columns)
    
    def pretty_print(self):
        exp = """Experiment {
            name: ...
            file: ...
            sleep: number,
            age: range(0, 10),
        }
        """
        return exp

exp = Experiment.load('Motivation', 'motivation2.csv')
sleep = exp.column('data_fun')
import pdb; pdb.set_trace()
sleep.normal()
print(exp.pretty_print())

