import tea
from tea.runtimeDataStructures.variable import NominalVariable, OrdinalVariable, NumericVariable

import pandas as pd 
import copy 

def test_load_data_csv(): 
    file_path = "./datasets/UScrime.csv"

    df = pd.read_csv(file_path)
    
    data_obj = tea.data(file_path)

    assert(df.equals(data_obj.data))


def test_load_data_df(): 
    file_path = "./datasets/UScrime.csv"

    df = pd.read_csv(file_path)
    df2 = copy.deepcopy(df)
    
    data_obj = tea.data(df2)

    assert(df.equals(data_obj.data))

def test_df_copy(): 
    file_path = "./datasets/UScrime.csv"

    df = pd.read_csv(file_path)
    
    data_obj = tea.data(df)
    df = df.applymap(lambda x: x**2) # square all elements

    assert(df.equals(data_obj.data.applymap(lambda x: x **2)))

def test_define_nominal_variable(): 
    categories = ['0', '1']

    var = {
        'name': 'So',
        'data type': 'nominal',
        'categories': categories
    }

    vars = [var]

    vars_list = tea.define_variables(vars)
    var_0 = vars_list[0]
    assert(isinstance(var_0, NominalVariable))
    assert(var_0.categories == categories)

def test_define_nominal_variable_extract_categories(): 
    categories = ['0', '1']

    var = {
        'name': 'So',
        'data type': 'nominal'
    }

    vars = [var]

    vars_list = tea.define_variables(vars)
    var_0 = vars_list[0]
    assert(isinstance(var_0, NominalVariable))
    assert(var_0.categories == None)

def test_define_ordinal_variable(): 
    var = {
        'name': 'Grade',
        'data type': 'ordinal',
        'categories': ['0', '1', '2']
    }

    vars = [var]

    vars_list = tea.define_variables(vars)
    var_0 = vars_list[0]
    assert(isinstance(var_0, OrdinalVariable))

def test_define_ordinal_variable_error(): 
    var = {
        'name': 'Grade',
        'data type': 'ordinal'
    }

    vars = [var]

    vars_list = None
    try: 
        vars_list = tea.define_variables(vars)
    except:
        pass
    assert(vars_list == None)

def test_define_numeric_variable(): 
    var = {
        'name': 'Prob',
        'data type': 'numeric'
    }

    vars = [var]

    vars_list = tea.define_variables(vars)
    var_0 = vars_list[0]
    assert(isinstance(var_0, NumericVariable))

def test_define_interval_variable(): 
    var = {
        'name': 'Prob',
        'data type': 'interval'
    }

    vars = [var]

    vars_list = tea.define_variables(vars)
    var_0 = vars_list[0]
    assert(isinstance(var_0, NumericVariable))

def test_define_ratio_variable(): 
    var = {
        'name': 'Prob',
        'data type': 'ratio'
    }

    vars = [var]

    vars_list = tea.define_variables(vars)
    var_0 = vars_list[0]
    assert(isinstance(var_0, NumericVariable))