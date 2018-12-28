from .ast import *
from .dataset import Dataset

from scipy import stats # Stats library used
import numpy as np # Use some stats from numpy instead

def evaluate(dataset: Dataset, statistic: Node): 
    if isinstance(statistic, Mean): 
        var = statistic.var 
        var_data = dataset.get_data(var)
        # If numeric type
        if (var.dtype == DataType.INTERVAL or var.dtype == DataType.RATIO): 
            return np.mean(var_data)
        elif (var.dtype == DataType.ORDINAL): 
            order = var.categories
            order_data = [order[d] for i,d in enumerate(var_data)]
            return np.mean(order_data)
        else: #(var.dtype == DataType.NOMINAL)
            raise Exception('Cannot calculate MEAN for NOMINAL data!')
    elif isinstance(statistic, Median): 
        var = statistic.var 
        var_data = dataset.get_data(var)
        # If numeric type
        if (var.dtype == DataType.INTERVAL or var.dtype == DataType.RATIO): 
            return np.median(var_data)
        elif (var.dtype == DataType.ORDINAL): 
            order = var.categories
            order_data = [order[d] for i,d in enumerate(var_data)]
            return np.median(order_data)
        else: #(var.dtype == DataType.NOMINAL)
            raise Exception('Cannot calculate MEDIAN for NOMINAL data!')
    elif isinstance(statistic, StandardDeviation):
        var = statistic.var 
        var_data = dataset.get_data(var)
        # If numeric type
        if (var.dtype == DataType.INTERVAL or var.dtype == DataType.RATIO): 
            return np.std(var_data)
        elif (var.dtype == DataType.ORDINAL): 
            order = var.categories
            order_data = [order[d] for i,d in enumerate(var_data)]
            return np.std(order_data)
        else: #(var.dtype == DataType.NOMINAL)
            raise Exception('Cannot calculate STANDARD DEVIATION for NOMINAL data!')
    elif isinstance(statistic, Variance):
        var = statistic.var 
        var_data = dataset.get_data(var)
        # If numeric type
        if (var.dtype == DataType.INTERVAL or var.dtype == DataType.RATIO): 
            return np.var(var_data)
        elif (var.dtype == DataType.ORDINAL): 
            order = var.categories
            order_data = [order[d] for i,d in enumerate(var_data)]
            return np.var(order_data)
        else: #(var.dtype == DataType.NOMINAL)
            raise Exception('Cannot calculate VARIANCE for NOMINAL data!')
    elif isinstance(statistic, Kurtosis): 
        var = statistic.var 
        var_data = dataset.get_data(var)
        # If numeric type
        if (var.dtype == DataType.INTERVAL or var.dtype == DataType.RATIO): 
            return stats.kurtosis(var_data)
        elif (var.dtype == DataType.ORDINAL): 
            # TODO: Does calculating kurtosis for ordinal data make any sense?
            order = var.categories
            order_data = [order[d] for i,d in enumerate(var_data)]
            return stats.kurtosis(order_data)
        else: #(var.dtype == DataType.NOMINAL)
            raise Exception('Cannot calculate KURTOSIS for NOMINAL data!')
    elif isinstance(statistic, Skew):  
        var = statistic.var 
        var_data = dataset.get_data(var)
        # If numeric type
        if (var.dtype == DataType.INTERVAL or var.dtype == DataType.RATIO): 
            return stats.skew(var_data)
        elif (var.dtype == DataType.ORDINAL): 
            # TODO: Does calculating skew for ordinal data make any sense?
            order = var.categories
            order_data = [order[d] for i,d in enumerate(var_data)]
            return stats.skew(order_data)
        else: #(var.dtype == DataType.NOMINAL)
            raise Exception('Cannot calculate SKEW for NOMINAL data!')
    elif isinstance(statistic, Normality): 
        var = statistic.var 
        var_data = dataset.get_data(var)
        # If numeric type
        if (var.dtype == DataType.INTERVAL or var.dtype == DataType.RATIO): 
            return (stats.kurtosistest(var_data), stats.skewtest(var_data))
        elif (var.dtype == DataType.ORDINAL): 
            # TODO: Does calculating kurtosis for ordinal data make any sense?
            order = var.categories
            order_data = [order[d] for i,d in enumerate(var_data)]
            return (stats.kurtosistest(order_data), stats.skewtest(order_data))
        else: #(var.dtype == DataType.NOMINAL)
            raise Exception('Cannot test SKEW or KURTOSIS for NOMINAL data!')
    elif isinstance(statistic, Frequency):
        # TODO: How to treat frequency of numeric vs. categorical data! 
        # Should ask for bins/rules to derive bins for numeric data?
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
    elif isinstance(statistic, Model):
        pass

    else: 
        raise Exception('Do not support this operation yet!')
#  'kurtosis', 'mean', 'minmax', 'nobs', 'skewness', 'variance'

# def evaluate_bivariate(dataset: Dataset, statistic: Test, var: Variable, var_data: pd.Series): 
#     pass


# # Prints/Returns to the user some nice representation of the statistic calculated
# def pretty_print(statistic_results: list): 
    
#     for stat in statistic_results: 
#         print(stat)
#         # print(stat_name, statistic)




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
