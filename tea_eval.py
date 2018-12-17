from tea_ast import *

from scipy import stats # Stats library used
import numpy as np # Use some stats from numpy instead
 
#  'kurtosis', 'mean', 'minmax', 'nobs', 'skewness', 'variance'


## TODO: Min? Max? 
univariate_stats = {'mean': UnivariateTest.mean, 
                    'median': UnivariateTest.median,
                    'standard deviation': UnivariateTest.std_dev,
                    'variance': UnivariateTest.variance, 
                    'kurtosis': UnivariateTest.kurtosis,
                    'skew': UnivariateTest.skew,
                    'normality': UnivariateTest.normality,
                    'frequency': UnivariateTest.frequency}


def evaluate(dataset: Dataset, statistic: Test, var: Variable, var_data: pd.Series): 
    if isinstance(statistic, UnivariateTest): 
        evaluate_univariate(dataset, statistic, var, var_data)
    elif isinstance(statistic, BivariateTest):
        evaluate_bivariate(dataset, statistic, var, var_data)
    else: 
        raise Exception('Not a valid action?!')
            

def evaluate_univariate(dataset: Dataset, statistic: Test, var: Variable, var_data: pd.Series): 
    var_categories_order = var.categories

    if isinstance(statistic, Mean): 
        # output = stats.describe(var_dat) #.dropna())
        # return getattr(output, 'mean')
        return np.mean(var_data)
    elif isinstance(statistic, Median): 
        return np.median(var_data)
    elif isinstance(statistic, StandardDeviation): 
        return np.std(var_data)
    elif isinstance(statistic, Variance): 
        return np.var(var_data)
    elif isinstance(statistic, Kurtosis): 
        # second value is test for normal kurtosis
        return (stats.kurtosis(var_data), stats.kurtosistest(var_data))
    elif isinstance(statistic, Skew):
        # second value is test for 0 skew
        return (stats.skew(var_data), stats.skewtest(var_data))
    elif isinstance(statistic, Normality):
        # test for kurtosis and skew
        # TODO: Provide a better interpretation of the results from these tests
        return (stats.kurtosistest(var_data), stats.skewtest(var_data))
        
    elif isinstance(statistic, Mean_Ordinal):
        order_data = [var_categories_order[d] for i,d in enumerate(var_data)]
        return np.mean(order_data)
    elif isinstance(statistic, Median_Ordinal): 
        order_data = [var_categories_order[d] for i,d in enumerate(var_data)]
        return np.median(order_data)
    elif isinstance(statistic, StandardDeviation_Ordinal):
        order_data = [var_categories_order[d] for i,d in enumerate(var_data)]
        return np.std(order_data)
    elif isinstance(statistic, Variance_Ordinal):
        order_data = [var_categories_order[d] for i,d in enumerate(var_data)]
        return np.var(order_data)
    elif isinstance(statistic, Kurtosis_Ordinal): 
        order_data = [var_categories_order[d] for i,d in enumerate(var_data)]
        # second value is test for normal kurtosis
        return (stats.kurtosis(order_data), stats.kurtosistest(order_data))
    elif isinstance(statistic, Skew_Ordinal):
        order_data = [var_categories_order[d] for i,d in enumerate(var_data)]
        # second value is test for 0 skew
        return (stats.skew(order_data), stats.skewtest(order_data))
    elif isinstance(statistic, Normality_Ordinal):
        order_data = [var_categories_order[d] for i,d in enumerate(var_data)]
        # test for kurtosis and skew
        # TODO: Provide a better interpretation of the results from these tests
        return (stats.kurtosistest(order_data), stats.skewtest(order_data))

    elif isinstance(statistic, Frequency_Categorical):
        import pdb; pdb.set_trace()
        frequency_summary = []
        t = CategoricalDtype(categories=var_categories_order.keys(), ordered=True)
        series = pd.Series(var_data, dtype=t)

        num_values = series.describe().count()
        most_frequent = series.describe().top
        most_frequent_count = series.describe().freq
        # TODO check for NaN
        idx = [i for i,s in enumerate(series) if (pd.isnull(s))] 

        statistics = ['Num values', 'Most frequent', 'Most frequent occurs', 'Nan data']
        calc = [num_values, most_frequent, most_frequent_count, idx]
        for i,s in enumerate(statistics):
            frequency_summary.append((statistics[i], calc[i]))
        # TODO feed into histogram for visualization

    else: 
        raise Exception('Not support this calculation yet!')


def evaluate_bivariate(dataset: Dataset, statistic: Test, var: Variable, var_data: pd.Series): 
    pass


# Prints/Returns to the user some nice representation of the statistic calculated
def pretty_print(stat_name: str, statistic): 
    print(stat_name, statistic)




# # dataset, group, outcome, characteristics
# test_comparison('dataset', {
#     'groups': 'gender',
#     'outcome': 'NFC',
#     'characteristics': ['multicollinearity']
# }

# # Allow filtering
# test_comparison('dataset', 'study', 'age', ['multicollinearity'], {'task':'arithmetic'})


# # use Python assignment?
# model1  = create_model('dataset', { 
#     'name':'BI model',
#     'type': 'logistic regression',
#     'dependent variable': 'BI',
#     'independent variable': 'AT',
#     'direction': 'forward'
# }) 
