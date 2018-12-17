# Purpose: First attempt to implementing Tea-lang VERY SIMPLY - written as shallowly embedded in Python

import pdb
import os
import csv
import attr
import pandas as pd
import numpy as np

from enum import Enum

from scipy import stats # Stats library used 
from pandas.api.types import CategoricalDtype

BASE_PATH = os.getcwd()

class Data_Type(Enum):
    ORDINAL = 0
    NOMINAL = 1
    INTERVAL = 2 # for CALCULATIONS, INTERVAL vs. RATIO data is not important distinction
    RATIO = 3 # for INTERPRETATIONS, important distinction

    # Means for ordinal data is contentious


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
        self.num_order = None # had a numeric version of the ordering??

    # def __repr__(self):
        # return f"Variable of type {self.data_type} with categories {self.categories} in the order {self.order}"
    
    # def __str__(self):
    #     return f"Variable of type {self.data_type} with categories {self.categories} in the order {self.order}"

# @attr.s(auto_attribs=True, hash=True, init=False)
class Dataset(object):
    # source: str
    # name: str
    # order: list
    # order could be treated as array of tuples (variable name, )
    def __init__(self, name, source_name, order=None):
        self.name = name
        assert(source_name.endswith('.csv')) # Only accept CSVs for now
        self.source = BASE_PATH + '/Datasets/' + source_name

        self.load_data(self.source)
        self.initialize_variables(order) # pass order array into separate function
    

    def load_data(self, source):
        data = pd.read_csv(source)

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


            duplicates = []
        else:  # Only assign data to dataset if there are not variable name collisions
            self.data = data


    # TODO may need to regularize strings 
    def initialize_variables(self, order):
        
        # FOR DEVLOPMENT
        order = [('study_name', 'nominal', ['aesthetics' ]), ('ip_country', 'nominal', ['United States', 'Canada'])]
        # source_file_path = BASE_PATH + '/Datasets/' + self.source

        self.variables = list() # list of pointers to Variable objects for each variable in dataset

        variable_names = self.data.columns.values.tolist() # cast from numpy.ndarray to list
        self.variable_names = self.data.columns.values.tolist() #TODO for DEBUGGING

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

    # UNIVARIATE ANALYSES
    # @param variable_name is the name of the variable of interest
    # @param characteristics: list of specific characteristics interested in, default is to output all info
    def explore_summary(self, variable_name, characteristics):
        ## TODO SUMMARIZE THE CHARACTERISTICS!!!

        # check that var exists in this dataset
        idx = self.get_variable_idx(variable_name)
        var = self.variables[idx]
        
        data_type = var.data_type

        summary = []

        if data_type is Data_Type.INTERVAL or data_type is Data_Type.RATIO:
            statistics = ['kurtosis', 'mean', 'minmax', 'nobs', 'skewness', 'variance']
            output = stats.describe(pd.Series(var.data).dropna())
            for stat in statistics: 
                summary.append((stat,getattr(output, stat))) # TODO How do we interpret distribution as normal? residuals?

        elif data_type is Data_Type.NOMINAL: 
            # May want to use Pandas (https://pandas.pydata.org/pandas-docs/stable/categorical.html#description)
            
            # cat = pd.Categorical(var.data, categories=var.categories
            t = CategoricalDtype(categories=var.categories, ordered=True)
            series = pd.Series(var.data, dtype=t)

            num_values = series.describe().count()
            most_frequent = series.describe().top
            most_frequent_count = series.describe().freq
            idx = [i for i,s in enumerate(series) if (pd.isnull(s))] # TODO check for NaN

            statistics = ['Num values', 'Most frequent', 'Most frequent occurs', 'Nan data']
            calc = [num_values, most_frequent, most_frequent_count, idx]
            for i,s in enumerate(statistics):
                summary.append((statistics[i], calc[i]))
            # TODO feed into histogram for visualization

        elif data_type is Data_Type.ORDINAL:
            # TODO ??? - depends on coding and integer mapping?? Is there a best practice?
            t = CategoricalDtype(categories=var.categories, ordered=True)
            series = pd.Series(var.data, dtype=t)

            # For NOMINAL data
            nominal_statistics = ['Num values', 'Most frequent', 'Most frequent occurs']
            calc = [num_values, most_frequent, most_frequent_count]
            for i,n in enumerate(nominal_statistics): 
                summary.append((nominal_statistics[i], calc[i]))

            #TODO should call this "ratio_statistics" instead??
            # For INTERVAL/RATIO data
            interval_statistics = ['kurtosis', 'mean', 'minmax', 'nobs', 'skewness', 'variance'] 
            output = stats.describe(series.dropna())
            for stat in interval_statistics:
                summary.append((stat,getattr(output, stat)))

        else: 
            raise Exception()


        return summary # then send to some pretty_print (generic?) function to output to user

    # BIVARIATE ANALYSES
    # @param filter is an array/list of bins -- can be statistical properties or user-defined
    def compare(self, groups, outcome, filter, characteristics=None):
        idx = self.get_variable_idx(groups)
        var = self.variables[idx]

        if (var.data_type is Data_Type.NOMINAL or var.data_type is Data_Type.ORDINAL):
            # bins = var.categories
            group_split = [g for i,g in self.data.groupby(groups)]
            bins = list()
            for g in group_split:
                bins.append(g[groups].unique()[0])
            pdb.set_trace()
            # Homoscedasticity

            # Multicollinearity

            # Residuals

            # Apply filter

            # Intercorrelation matrix??
        elif (var.data_type is Data_Type.INTERVAL or var.data_type is Data_Type.RATIO):
            pass
        else: 
            raise Exception(f"Grouping based on {var} ({var.data_type}) is not possible.")



        
    # def __repr__(self):
    #     return f"Dataset named {self.name} from {self.source}"

    # def __str__(self):
    #     return f"Dataset named {self.name} from {self.source}"


# var = Variable(Data_Type.ORDINAL, categories = ['high school', 'college', 'graduate'], order = [0, 1, 2])


    # Helper method to see if variable passed as @param exists in dataset
    # @ Returns index of variable in dataset
    def get_variable_idx(self, variable_name): 
        idx = [i for i, v in enumerate(self.variables) if v.name == variable_name] 

        if (len(idx) == 0):
            raise Exception('Variable does not exist in this dataset')
        else: 
            return idx.pop()

        ## When load data, already check that no two columns/variables share names
        

data = Dataset('test', 'test.csv') # load data
summary = data.explore_summary('age', ['distribution', 'mean', 'median']) # summary
study = data.explore_summary('study_name', None)
c = data.compare('ip_country', None, None)
pdb.set_trace()