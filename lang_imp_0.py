# Purpose: First attempt to implementing Tea-lang VERY SIMPLY - written as shallowly embedded in Python

import pdb
import os
import csv
import attr
import pandas as pd

from enum import Enum

BASE_PATH = os.getcwd()

class Data_Type(Enum):
    ORDINAL = 0
    NOMINAL = 1
    INTERVAL = 2
    RATIO = 3

@attr.s(auto_attribs=True, hash=True, init=False)
class Variable(object):
    name: str
    data_type: Data_Type
    categories: list
    order: list
    data: list
    def __init__(self, name, data_type, data, categories=None, order=None):
        self.name = name # should check that this exists in the dataset before creating
        self.data_type = data_type
        self.data = data

        if (self.data_type is Data_Type.INTERVAL or self.data_type is Data_Type.RATIO): 
            assert(categories == order == None)
        if (self.data_type is Data_Type.ORDINAL or self.data_type is Data_Type.NOMINAL):
            assert(categories != None)
        self.categories = categories
        if (self.data_type is self.data_type is Data_Type.ORDINAL):
            assert(order != None)
        self.order = order # stores indices of the categories in ascending order

    # def __repr__(self):
    #     return f"Variable of type {self.data_type} with categories {self.categories} in the order {self.order}"
    
    # def __str__(self):
    #     return f"Variable of type {self.data_type} with categories {self.categories} in the order {self.order}"

# @attr.s(auto_attribs=True, hash=True, init=False)
class Dataset(object):
    # source: str
    # name: str
    # order: list
    # order could be treated as array of tuples (variable name, )
    def __init__(self, name, source, order=None):
        self.name = name
        assert(source.endswith('.csv')) # Only accept CSVs for now
        self.source = source

        self.initialize_variables(order) # pass order array into separate function
    
    def initialize_variables(self, order):
        # FOR DEVLOPMENT
        order = [('boo', 'ordinal', ['urban', 'rural']), ('urban', 'ordinal', ['urban', 'rural'])]
        source_file_path = BASE_PATH + '/Datasets/' + self.source

        self.variables = list() # list of pointers to Variable objects for each variable in dataset

        self.data = pd.read_csv(source_file_path)
        variable_names = self.data.columns.values.tolist() # cast from numpy.ndarray to list

        for var_name in variable_names: 
            # Variable(NAME, TYPE, CATEGORIES, ORDER)
            var_dataType = None
            var_categories = None
            var_order = None
            
            idx = [i for i, t in enumerate(order) if t[0] == var_name]
            if (len(idx) == 0):
                # Treat as a numeric value
                var_dataType = Data_Type.INTERVAL # TODO Does INTERVAL vs. RATIO CHANGE ANALYSES???
            elif (len(idx) == 1):
                idx = idx.pop()
                var_info = order[idx]
                if (var_info[1] == 'ordinal'):
                    var_dataType = Data_Type.ORDINAL
                    var_categories = var_info[2]
                    var_order = [i[0] for i in enumerate(var_categories)]
                elif (var_info[1] == 'nominal'):
                    var_dataType = Data_Type.NOMINAL
                    var_categories = var_info[2]
                else: 
                    raise Exception('Declared categories for data that is neither ORDINAL nor INTERVAL')
            else: 
                # TODO May want to change this
                raise Exception('Variable order declared twice')
            
            self.variables.append(Variable(var_name, var_dataType, self.data[var_name].tolist(), var_categories, var_order)) ## Include pointer to dataset?


        pdb.set_trace()

        # TODO may need to regularize strings 
        # with open(source_file_path, 'r', encoding='utf-8-sig') as tmp_file: 
        #     tmp_reader = csv.reader(tmp_file)
        #     variable_names = next(tmp_reader)

        # with open(source_file_path, 'r') as csvfile: 
        #     reader = csv.DictReader(csvfile, fieldnames=variable_names)

        #     pdb.set_trace()
    
    # def __repr__(self):
    #     return f"Dataset named {self.name} from {self.source}"

    # def __str__(self):
    #     return f"Dataset named {self.name} from {self.source}"


# var = Variable(Data_Type.ORDINAL, categories = ['high school', 'college', 'graduate'], order = [0, 1, 2])

data = Dataset('test', 'test.csv')
pdb.set_trace()