# from tea import load_data,  explore_summary
from tea import evaluate, ordinal, nominal, interval, ratio, load_data, mean

from collections import OrderedDict
import numpy as np

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
    r = ratio('age', range=[0, 99])
    assert r.name == 'age'
    assert r.categories == None
    assert r.drange == [0, 99]

def test_load_data(): 
    variables = [ordinal('education', ['high school', 'college', 'PhD']), ratio('age', range=[0,99])]
    file_path = './datasets/mini_test.csv'
    ds = load_data(file_path, variables)

    assert ds.dfile == file_path
    assert ds.variables == variables

variables = [ordinal('education', ['high school', 'college', 'PhD']), ratio('age', range=[0,99])]
file_path = './datasets/mini_test.csv'
ds = load_data(file_path, variables)
age_data = [32,35,45,23,50,32,35,45,23,50]
edu_data = ['high school','college','high school','PhD','PhD','high school','college','high school','PhD','PhD']
edu_num = [1,2,1,3,3,1,2,1,3,3]
def test_mean_num(): 
    age = ds.get_variable('age')
    assert evaluate(ds, mean(age)) == np.mean(age_data)

def test_mean_ordinal(): 
    edu = ds.get_variable('education')
    assert evaluate(ds, mean(edu)) == np.mean(edu_num)

    # ds = load_data('./dataasets/mini_test.csv', [ 
    #     {
    #         'name': 'education',
    #         'dtype': DataType.ORDINAL,
    #         'categories': ['high school', 'college', 'PhD'],
    #         'drange': None
    #     }, 
    #     {
    #         'name': 'age',
    #         'dtype': DataType.RATIO,
    #         'categories': None,
    #         'drange': [0,99]
    #     }
    # ])
#     ds = Dataset()
#     ds.load_data(source)

#     for var_name in vars: 
#         v = vars[var_name]
#         data_type = None
#         categories = None
#         if (v['type'] == 'ordinal' or v['type'] == 'nominal'): 
#             # Create order tuple
#             categories = OrderedDict()
#             for i, c in enumerate(v['categories']):
#                 categories[c] = i+1
#         if (v['type'] == 'ordinal'): 
#             data_type = DataType.ORDINAL
#         elif (v['type'] == 'nominal'): 
#             data_type = DataType.NOMINAL
#         elif (v['type'] == 'interval'): 
#             data_type = DataType.INTERVAL
#         elif (v['type'] == 'ratio'): 
#             data_type = DataType.RATIO
#         else: 
#             raise Exception('Variables must be specified as being ordinal, nominal, interval, or ratio')
#         ds.set_variable(var_name, data_type, categories)
    

# def test():
#     assert True

# def test_prog1():
#     ############ TEST PROGRAM ###########
#     dataset1 = load_data('mini_test.csv', {
#         'education': {
#             'type': 'ordinal', 
#             'categories': ['high school', 'college', 'PhD']
#         }, 
#         'age': {
#             'type': 'ratio'
#         }
#     })

#     explore_summary('dataset1', {
#         'variable': 'age',
#         'characteristics': ['mean', 'median', 'standard deviation', 'variance']
#     })

#     explore_summary('dataset1', {
#         'variable': 'education',
#         'characteristics': ['frequency']
#         # 'characteristics': ['mean', 'median', 'standard deviation', 'variance']
#     })

#     # test comparison()

