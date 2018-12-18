# from tea import load_data,  explore_summary
from tea import ordinal, nominal, interval, ratio

from collections import OrderedDict

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

