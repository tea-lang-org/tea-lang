from tea import (   load_data,
                    const,
                    ordinal, isordinal, 
                    nominal, isnominal,
                    interval, isinterval,
                    ratio, isratio, isnumeric,
                    select,
                    evaluate,
                    compare, predict
                )

from collections import OrderedDict
import numpy as np
import pandas as pd
from scipy import stats
import statsmodels.api as sm

# Sample program
"""
load_data('data.csv')
design_experiment({
    'independent variable': ['col_name', 'col_name'],
    'dependent variable': ['col_name'],
    # not sure that we want to call them "between" and "within" subjects -- may want to elicit separately or via a different modality
    'between subjects': ['col_name'],
    'within subjects': ['col_name']
})
compare('groups', 'time') # may want to go back to the original doc
"""

def test_make_ordinal():
    o = ordinal('education', ['high school', 'college', 'Master\'s', 'PhD'])
    assert o.name == 'education'
    assert o.categories == OrderedDict([
        ('high school', 1),
        ('college', 2),
        ('Master\'s', 3),
        ('PhD', 4)
    ])
    assert o.drange == [1,4]

def test_make_nominal():
    n = nominal('gender', ['male', 'female', 'non-binary'])
    assert n.name == 'gender'
    assert n.categories == OrderedDict([
        ('male', -1),
        ('female', -1),
        ('non-binary', -1)
    ])
    assert n.drange == None

def test_make_interval(): 
    i = interval('temp', [36, 115])
    assert i.name == 'temp'
    assert i.categories == None
    assert i.drange == [36, 115]

def test_make_ratio(): 
    r = ratio('age', drange=[0, 99])
    assert r.name == 'age'
    assert r.categories == None
    assert r.drange == [0, 99]

def test_load_data(): 
    variables = [ordinal('education', ['high school', 'college', 'PhD']), ratio('age', drange=[0,99])]
    file_path = './datasets/mini_test.csv'
    ds = load_data(file_path, variables, 'participant_id')

    assert ds.dfile == file_path
    assert ds.variables == variables

categories = ['high school', 'college', 'PhD']
# variables = [ordinal('education', categories)]
edu = ordinal('education', ['high school', 'college', 'PhD'])
age = ratio('age', drange=[0,99])
variables = [edu, age]
file_path = './datasets/mini_test.csv'
ds = load_data(file_path, variables, 'participant_id')

def test_index_in_dataset():
    for v in variables:
        assert(ds[v.name].equals(ds.data[v.name]))
    
def test_select_equals(): 
    for v in variables: 
        all_unique = ds.data[v.name].unique()

        for e in all_unique: 
            res = select(v, '==', const(e))
            sub_ds = evaluate(ds, res).dataframe
            tmp = ds.data[v.name]
            assert (sub_ds.equals(tmp[tmp == e]))

def test_select_not_equals(): 
    for v in variables: 
        all_unique = ds.data[v.name].unique()
        for e in all_unique: 
            res = select(v, '!=', const(e))
            sub_ds = evaluate(ds, res).dataframe
            tmp = ds.data[v.name]
            assert (sub_ds.equals(tmp[tmp != e]))

def test_select_lt(): 
    for v in variables: 
        if (v.drange): # is ORDINAL or INTERVAL/RATIO
            if (isordinal(v)):
                categories = v.categories.keys()
                for cat in categories:
                    num = v.categories[cat]
                    res_str = select(v, '<', const(cat))
                    res_num = select(v, '<', const(num))
                    sub_ds_str = evaluate(ds, res_str).dataframe
                    sub_ds_num = evaluate(ds, res_num).dataframe
                    
                    # Selecting using STR or INT should give same answer
                    tmp_res = list(filter(lambda x: v.categories[x] < v.categories[cat], ds.data[v.name]))
                    # TODO: ??? Checking for "user equivalence" -- that the data that is selected is what I expect to be selected
                    assert (sub_ds_str.tolist() == tmp_res)
                    assert (sub_ds_num.tolist() == tmp_res)
                    
            elif (isnumeric(v)):
                drange = v.drange
                midpoint = (drange.pop() - drange.pop(0))/2
                res = select(v, '<', const(midpoint))
                sub_ds = evaluate(ds, res).dataframe

                data = ds.data[v.name]
                tmp = data[data < midpoint]
                assert(sub_ds.equals(tmp))

def test_select_le(): 
    for v in variables: 
        if (v.drange): # is ORDINAL or INTERVAL/RATIO
            if (isordinal(v)):
                categories = v.categories.keys()
                for cat in categories:
                    num = v.categories[cat]
                    res_str = select(v, '<=', const(cat))
                    res_num = select(v, '<=', const(num))
                    sub_ds_str = evaluate(ds, res_str).dataframe
                    sub_ds_num = evaluate(ds, res_num).dataframe
                    
                    # Selecting using STR or INT should give same answer
                    tmp_res = list(filter(lambda x: v.categories[x] <= v.categories[cat], ds.data[v.name]))
                    # TODO: ??? Checking for "user equivalence" -- that the data that is selected is what I expect to be selected
                    assert (sub_ds_str.tolist() == tmp_res)
                    assert (sub_ds_num.tolist() == tmp_res)
                    
            elif (isnumeric(v)):
                drange = v.drange
                midpoint = (drange.pop() - drange.pop(0))/2
                res = select(v, '<=', const(midpoint))
                sub_ds = evaluate(ds, res).dataframe

                data = ds.data[v.name]
                tmp = data[data <= midpoint]
                assert(sub_ds.equals(tmp))

def test_select_gt(): 
    for v in variables: 
        if (v.drange): # is ORDINAL or INTERVAL/RATIO
            if (isordinal(v)):
                categories = v.categories.keys()
                
                # cat_num = v.categories.values()
                for cat in categories:
                    num = v.categories[cat]
                    res_str = select(v, '>', const(cat))
                    res_num = select(v, '>', const(num))
                    sub_ds_str = evaluate(ds, res_str).dataframe
                    sub_ds_num = evaluate(ds, res_num).dataframe
                    
                    # Selecting using STR or INT should give same answer
                    tmp_res = list(filter(lambda x: v.categories[x] > v.categories[cat], ds.data[v.name]))
                    # TODO: ??? Checking for "user equivalence" -- that the data that is selected is what I expect to be selected
                    assert (sub_ds_str.tolist() == tmp_res)
                    assert (sub_ds_num.tolist() == tmp_res)
                    
            elif (isnumeric(v)):
                drange = v.drange
                midpoint = (drange.pop() - drange.pop(0))/2
                res = select(v, '>', const(midpoint))
                sub_ds = evaluate(ds, res).dataframe

                data = ds.data[v.name]
                tmp = data[data > midpoint]
                assert(sub_ds.equals(tmp))

def test_select_ge(): 
    for v in variables: 
        if (v.drange): # is ORDINAL or INTERVAL/RATIO
            if (isordinal(v)):
                categories = v.categories.keys()
                
                # cat_num = v.categories.values()
                for cat in categories:
                    num = v.categories[cat]
                    res_str = select(v, '>=', const(cat))
                    res_num = select(v, '>=', const(num))
                    sub_ds_str = evaluate(ds, res_str).dataframe
                    sub_ds_num = evaluate(ds, res_num).dataframe
                    
                    # Selecting using STR or INT should give same answer
                    tmp_res = list(filter(lambda x: v.categories[x] >= v.categories[cat], ds.data[v.name]))
                    # TODO: ??? Checking for "user equivalence" -- that the data that is selected is what I expect to be selected
                    assert (sub_ds_str.tolist() == tmp_res)
                    assert (sub_ds_num.tolist() == tmp_res)
                    
            elif (isnumeric(v)):
                drange = v.drange
                midpoint = (drange.pop() - drange.pop(0))/2
                res = select(v, '>=', const(midpoint))
                sub_ds = evaluate(ds, res).dataframe

                data = ds.data[v.name]
                tmp = data[data >= midpoint]
                assert(sub_ds.equals(tmp))

# Bivariate test, between subjects
# X: Categorical (nominal) | Y: Numeric (ratio)
condition = nominal('condition', ['microtask', 'macrotask'])
accuracy = ratio('accuracy', drange=[0,50])
age = ratio('age', drange=[0,99])
variables = [condition, accuracy, age]
file_path = './datasets/bivariate_mini.csv'
experimental_design = {
                        'participant id': 'participant_id',
                        'independent variables': 'condition',
                        'dependent variables': 'accuracy',
                        'between subjects': 'condition',
                        # 'alpha': 1
                    }
ds = load_data(file_path, variables, 'participant_id')

# Bivariate test, between subjects
# X: Numeric (ratio) | Y: Numeric (ratio)
def test_compare_bivariate_between_cat_num():
    stat = compare(condition, accuracy, 'microtask > macrotask') # if we want to select only a couple conditions, we can do that too
    res = evaluate(ds, stat, experimental_design)
    print(res)

    # assert (res.test_results[1] < .05) # need to write better tests 

def test_compare_bivariate_between_num_num(): 
    stat = compare(age, accuracy) # if we want to select only a couple conditions, we can do that too
    res = evaluate(ds, stat, experimental_design)
    print(res) # write prettier str


def test_compare_bivariate_within_cat_num(): 
    pass

def test_compare_variant_ds(): 
    variant = interval('variant', drange=[1,267]) #Is there a better way to shortcut cateories -- if we wanted to call this column nominal? 
    naive_time = ratio('naive', drange=[0,1000]) # does it make sense to require a drange for ratio data? (supposed to be used for filtering)
    caching_time = ratio('caching', drange=[0,1000])
    forking_time = ratio('forking', drange=[0,1000])
    equivalent = nominal('equivalent', ['0', '1']) # what if I did 0 and 1 in no strings? 
    first_order = nominal('first.order', ['0', '1']) # what if I did 0 and 1 in no strings? 
    run = interval('run', drange=[1,5])
    subject = nominal('subject', ['tictactoe', 'tax', 'triangle'])

    variables = [variant, naive_time, caching_time, forking_time, equivalent, first_order, run, subject]
    file_path = './datasets/timing.csv'
    experimental_design = {
                            # 'participant id': 'participant_id'
                            'independent variables': 'subject',
                            'dependent variables': ['forking', 'caching', 'naive'],
                            'between subjects': 'subject',
                            'within subjects': 'run', # what if I put 'variant' here -- would there be a cross-checking that the things listed in design exhibit behavior that would expect from between and within subjects? 
                            # 'alpha': 1
                        }
    ds = load_data(file_path, variables, 'subject')
    

def test_dataset_query():
    condition = nominal('condition', ['microtask', 'macrotask'])
    accuracy = ratio('accuracy', drange=[0,50])
    variables = [condition, accuracy]
    file_path = './datasets/bivariate_mini.csv'
    
    experimental_design = {
                            'independent variables': 'condition',
                            'dependent variables': 'accuracy',
                            'between subjects': 'condition',
                            'participant id': 'participant_id'
                        }

    ds = load_data(file_path, variables, 'participant_id')

    ds.select('accuracy', ["condition == 'microtask'"]) # this is the correct way to build up a query