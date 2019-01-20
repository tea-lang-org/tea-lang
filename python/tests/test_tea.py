# from tea import load_data,  explore_summary
from tea import (   load_data,
                    const,
                    ordinal,
                    isordinal, 
                    # nominal
                    select,
                    evaluate
                )
# (evaluate, ordinal, nominal, interval, ratio, load_data, model, 
#             mean, median, standard_deviation, variance, kurtosis, skew, normality, frequency,
#             between_experiment, within_experiment, mixed_experiment, equation,
#             load_data_arrs, hypothesis, experiment_design)

from collections import OrderedDict
import numpy as np
from scipy import stats
import statsmodels.api as sm


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

# def test_make_nominal():
#     n = nominal('gender', ['male', 'female', 'non-binary'])
#     assert n.name == 'gender'
#     assert n.categories == OrderedDict([
#         ('male', -1),
#         ('female', -1),
#         ('non-binary', -1)
#     ])
#     assert n.drange == None

# def test_make_interval(): 
#     i = interval('temp', [36, 115])
#     assert i.name == 'temp'
#     assert i.categories == None
#     assert i.drange == [36, 115]

# def test_make_ratio(): 
#     r = ratio('age', range=[0, 99])
#     assert r.name == 'age'
#     assert r.categories == None
#     assert r.drange == [0, 99]

# def test_load_data(): 
#     variables = [ordinal('education', ['high school', 'college', 'PhD']), ratio('age', range=[0,99])]
#     file_path = './datasets/mini_test.csv'
#     ds = load_data(file_path, variables)

#     assert ds.dfile == file_path
#     assert ds.variables == variables

categories = ['high school', 'college', 'PhD']
variables = [ordinal('education', categories)]
# variables = [ordinal('education', ['high school', 'college', 'PhD']), ratio('age', range=[0,99])]
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

def test_select_less(): 
    for v in variables: 
        if (v.drange): # is ORDINAL or INTERVAL/RATIO
            if (isordinal(v)):
                cat_keys = v.categories.keys()
                # cat_num = v.categories.values()
                for c in cat_keys:
                    num = v.categories[c]
                    res_str = select(v, '<', const(c))
                    res_num = select(v, '<', const(num))
                    sub_ds_str = evaluate(ds, res_str)
                    # sub_ds_num = evaluate(ds, res_num).dataframe
                    import pdb; pdb.set_trace()

                    tmp_cat = ds.data[v.name]
                    tmp_num = [v.categories(n) for n in tmp_cat]
                    tmp_res = filter(lambda x: x < num, tmp_num)
                    # tmp = tmp_num[tmp_num <= e]
                    import pdb; pdb.set_trace()

                    assert (sub_ds_str.equals(tmp_res))
                    assert (sub_ds_num.equals(tmp_res))
            # elif (isnumeric(v)):
            #     pass


# age_data = [32,35,45,23,50,32,35,45,23,50]
# edu_data = ['high school','college','high school','PhD','PhD','high school','college','high school','PhD','PhD']
# edu_num = [1,2,1,3,3,1,2,1,3,3]
# def test_mean_num(): 
#     age = ds.get_variable('age')
#     assert evaluate(ds, mean(age)) == np.mean(age_data)

# def test_mean_ordinal(): 
#     edu = ds.get_variable('education')
#     assert evaluate(ds, mean(edu)) == np.mean(edu_num)

# def test_median_num(): 
#     age = ds.get_variable('age')
#     assert evaluate(ds, median(age)) == np.median(age_data)

# def test_median_ordinal(): 
#     edu = ds.get_variable('education')
#     assert evaluate(ds, median(edu)) == np.median(edu_num)

# def test_std_num(): 
#     age = ds.get_variable('age')
#     assert evaluate(ds, standard_deviation(age)) == np.std(age_data)

# def test_std_ordinal(): 
#     edu = ds.get_variable('education')
#     assert evaluate(ds, standard_deviation(edu)) == np.std(edu_num)

# def test_variance_num(): 
#     age = ds.get_variable('age')
#     assert evaluate(ds, variance(age)) == np.var(age_data)

# def test_variance_ordinal(): 
#     edu = ds.get_variable('education')
#     assert evaluate(ds, variance(edu)) == np.var(edu_num)

# def test_kurtosis_num(): 
#     age = ds.get_variable('age')
#     assert evaluate(ds, kurtosis(age)) == stats.kurtosis(age_data)

# def test_kurtosis_ordinal(): 
#     edu = ds.get_variable('education')
#     assert evaluate(ds, kurtosis(edu)) == stats.kurtosis(edu_num)

# def test_skew_num(): 
#     age = ds.get_variable('age')
#     assert evaluate(ds, skew(age)) == stats.skew(age_data)

# def test_skew_ordinal(): 
#     edu = ds.get_variable('education')
#     assert evaluate(ds, skew(edu)) == stats.skew(edu_num)

# def test_normality_num(): 
#     age = ds.get_variable('age')
#     assert evaluate(ds, normality(age)) == (stats.kurtosistest(age_data), stats.skewtest(age_data))

# def test_normality_ordinal(): 
#     edu = ds.get_variable('education')
#     assert evaluate(ds, normality(edu)) == (stats.kurtosistest(edu_num), stats.skewtest(edu_num))

# def test_frequency(): 
#     pass


# variables = [nominal('block_number', ['1', '2', '3', '4']), nominal('number_of_symbols_to_memorize', ['0', '1', '2', '3', '4', '6']), nominal('web_usage', ['1', '2', '3', '4'])]
# file_path = './datasets/2016.12.10-gajos17personality-data.csv'
# ds2 = load_data(file_path, variables)
# def test_between_experiment(): 
#     sets = ds2.get_variable('number_of_symbols_to_memorize')
#     sets_exp = between_experiment([sets])
#     assert sets_exp.between_vars == [sets]
#     assert sets_exp.within_vars == None

# def test_within_experiment(): 
#     block = ds2.get_variable('block_number')
#     block_exp = within_experiment([block])
#     assert block_exp.between_vars == None
#     assert block_exp.within_vars == [block]

# def test_mixed_experiment():
#     sets = ds2.get_variable('number_of_symbols_to_memorize')
#     block = ds2.get_variable('block_number')
#     mixed_exp = mixed_experiment([sets], [block])
#     assert mixed_exp.between_vars == [sets]
#     assert mixed_exp.within_vars == [block]

# # TODO: Write test case based on linear regression found in paper
# def test_build_equation(): 
#     sets = ds2.get_variable('number_of_symbols_to_memorize')
#     web = ds2.get_variable('web_usage')
#     block = ds2.get_variable('block_number')
#     eq = equation(sets + web + block + web*block)
#     assert eq.eq_handle == sets + web + block + web*block

# def test_build_model(): 
#     sets = ds2.get_variable('number_of_symbols_to_memorize')
#     web = ds2.get_variable('web_usage')
#     block = ds2.get_variable('block_number')
#     # exp = between_experiment([sets])
#     m = model(sets, (web + block) + web*block)
#     assert m.eq_independent_vars == web + block + web*block
#     assert m.dependent_var == sets

# variables = [interval('participant', ['1', '10']), nominal('condition', ['a', 'b']), ratio('accuracy', ['0', '10'])]
# file_path = './datasets/mini_test2.csv'
# ds3 = load_data(file_path, variables, 'participant')
# def test_build_hypothesis(): 
#     condition = ds3.get_variable('condition')
#     acc = ds3.get_variable('accuracy')
#     m = model(acc, condition)
#     h = hypothesis('a'>'b')
#     exp = experiment_design([condition, acc])
#     results = evaluate(ds3, exp, m, h)
    # TODO May want to do something similar to the summary() method -- https://www.statsmodels.org/stable/_modules/statsmodels/base/model.html#GenericLikelihoodModelResults.summary
    

# def test_model(): 
#     Y = [1,3,4,5,2,3,4]
#     X = range(1,8)

#     ds = load_data_arrs(Y, X)
#     X = sm.add_constant(X)

#     model = sm.OLS(Y,X)
#     results = model.fit()
#     stats = results._results.__dict__.keys()

#     for s in stats: 
#         # Do something
#         pass


#     import pdb; pdb.set_trace()


#     # ds = load_data('./dataasets/mini_test.csv', [ 
#     #     {
#     #         'name': 'education',
#     #         'dtype': DataType.ORDINAL,
#     #         'categories': ['high school', 'college', 'PhD'],
#     #         'drange': None
#     #     }, 
#     #     {
#     #         'name': 'age',
#     #         'dtype': DataType.RATIO,
#     #         'categories': None,
#     #         'drange': [0,99]
#     #     }
#     # ])
# #     ds = Dataset()
# #     ds.load_data(source)

# #     for var_name in vars: 
# #         v = vars[var_name]
# #         data_type = None
# #         categories = None
# #         if (v['type'] == 'ordinal' or v['type'] == 'nominal'): 
# #             # Create order tuple
# #             categories = OrderedDict()
# #             for i, c in enumerate(v['categories']):
# #                 categories[c] = i+1
# #         if (v['type'] == 'ordinal'): 
# #             data_type = DataType.ORDINAL
# #         elif (v['type'] == 'nominal'): 
# #             data_type = DataType.NOMINAL
# #         elif (v['type'] == 'interval'): 
# #             data_type = DataType.INTERVAL
# #         elif (v['type'] == 'ratio'): 
# #             data_type = DataType.RATIO
# #         else: 
# #             raise Exception('Variables must be specified as being ordinal, nominal, interval, or ratio')
# #         ds.set_variable(var_name, data_type, categories)
    

# # def test():
# #     assert True

# # def test_prog1():
# #     ############ TEST PROGRAM ###########
# #     dataset1 = load_data('mini_test.csv', {
# #         'education': {
# #             'type': 'ordinal', 
# #             'categories': ['high school', 'college', 'PhD']
# #         }, 
# #         'age': {
# #             'type': 'ratio'
# #         }
# #     })

# #     explore_summary('dataset1', {
# #         'variable': 'age',
# #         'characteristics': ['mean', 'median', 'standard deviation', 'variance']
# #     })

# #     explore_summary('dataset1', {
# #         'variable': 'education',
# #         'characteristics': ['frequency']
# #         # 'characteristics': ['mean', 'median', 'standard deviation', 'variance']
# #     })

# #     # test comparison()

