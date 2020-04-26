from typing import Union

import pandas as pd

from tea.runtimeDataStructures.dataset import Dataset
from tea.ast import (Variable, DataType, Literal, Relate, Relationship)

from collections import OrderedDict
from pathlib import Path

iv_identifier = 'independent variable'
dv_identifier = 'dependent variable'
var_identifier = 'variable'
categorical_prediction = 'categorical prediction'
continuous_prediction = 'continuous prediction'
categorical_prediction_delimiter = ':'
continuous_prediction_delimiter = '~'
categorical_comparators = ['>', '<', '==', '!=']
continuous_positive_relationship = '+'
continuous_negative_relationship = '-'


def const(val):
    return Literal(val)


def ordinal(var_name: str, ordered_categories: list):
    # Create order tuple
    categories = OrderedDict()
    for i, c in enumerate(ordered_categories):
        categories[c] = i + 1  # start at 1 not 0

    return Variable.from_spec(var_name, DataType.ORDINAL, categories, [1, len(categories)])


def isordinal(var: Variable):
    return var.dtype is DataType.ORDINAL


def nominal(var_name: str, unordered_categories: list):
    categories = OrderedDict()
    for i, c in enumerate(unordered_categories):
        categories[c] = -1
    return Variable.from_spec(var_name, DataType.NOMINAL, categories, None)


def isnominal(var: Variable):
    return var.dtype is DataType.NOMINAL


def interval(var_name: str, drange: list = None):
    return Variable.from_spec(var_name, DataType.INTERVAL, None,
                              drange)  # treat range like categories, check that all values are within range


def isinterval(var: Variable):
    return var.dtype is DataType.INTERVAL


def ratio(var_name: str, drange: list = None):
    return Variable.from_spec(var_name, DataType.RATIO, None,
                              drange)  # treat range like categories, check that all values are within range


def isratio(var: Variable):
    return var.dtype is DataType.RATIO


def isnumeric(var: Variable):
    return isratio(var) or isinterval(var)


def iscategorical(var: Variable):
    return isnominal(var) or isordinal(var)


# @param pid is the name of the column with participant ids
def load_data(source_name: Union[str, Path, pd.DataFrame], vars: list, pid: str):
    return Dataset(source_name, vars, pid)


def load_data_from_url(url: str, name: str):
    return Dataset.load(url, name)


def select(var: Variable, op: str, other: Literal):
    if op == '==':
        return var.subset_equals(other)
    elif op == '!=':
        return var.subset_not_equals(other)
    elif op == '<':
        return var.subset_lt(other)
    elif op == '<=':
        return var.subset_le(other)
    elif op == '>':
        return var.subset_gt(other)
    elif op == '>=':
        return var.subset_ge(other)
    else:
        raise ValueError(f"Do not support the operator{op}")


# @param vars: list of all vars in tuple form (Variable, 'iv/dv/variable')
# @param role: "role" of Variable (i.e., independent variable, dependent variable, variable)
# @returns new list of vars with specified role
# def get_vars(role: str, vars: list): 
#     vars_role = []
#     for v,r in vars:
#         if r == role: 
#             vars_role.append(v)

#     return vars_role

# TODO: need to check that the prediction is well-formed (VALUES that are ordered exist, for example)
"""
    Grammar for predictions: 
    # Cat x Numeric
    # what matters is that the var using to form groups in comparison is nominal/categorical 
    <, >, ==, != --> Tests null hypothesis that there is no difference OR ask for one-sidedness in tests (as constraint?)
    predict(groups: Variable, outcome: Variable, prediction: str=None)
    # Cat x Cat
    Frequency(??)
    predict(groups: Variable, outcome: Variable, prediction: str=None)
    # Numeric x Cat
    # we need to know which variable is factor vs. predictor
    logistic regression
    predict(var: Variable, outcome: Variable, prediction: str=None)
    # Numeric x Numeric --> Should allow for both
    # Need to know which variable is factor vs predictor
    Prediction: y ~ - var + var + var (e.g., time ~ + condition + age || prediction: condition:a > condition:b)
    Prediction: + var, - var
    predict(outcome: Variable, factors: list of variables, prediction: str=None)
    predict(factors: list, outcome: Variable, prediction: str=None)
    --> check type of outcome
    --> check number of factors: if > 1 then multivariate case else bivariate case, check for factor type
    --> in multivariate case, the types of factors don't have a bearing on the ....?
"""


# def is_var_in_list(var_name: str, vars: list):
#     names = [v.name for v in vars]

#     return var_name in names

def get_var_from_list(var_name: str, vars: list):
    for v in vars:
        if v.name == var_name:
            return v

    return None  # Does not exist


def is_well_formed_prediction(prediction_type: str, vars: list, prediction: str):
    # import pdb; pdb.set_trace()
    if categorical_prediction == prediction_type:
        var_ind = prediction.index(categorical_prediction_delimiter)
        var_name = prediction[:var_ind].strip()

        # Does the variable actually exist in the list of variables?
        var = get_var_from_list(var_name, vars)
        return var is not None
        # if var:
        #     # Does the category exist in the var? (implictly checks that var is a categorical variable)
        #     return var.category_exists(category)
        # else: 
        #     return ValueError(f"The variable used in prediction{var} is not in list of variables comparing{vars}")
    elif continuous_prediction == prediction_type:

        # Prediction includes categorical variable value
        if categorical_prediction_delimiter in prediction:
            cat_delimiter_ind = prediction.index(categorical_prediction_delimiter)
            num_delimiter_ind = prediction.index(continuous_prediction_delimiter)

            categorical_var_name = prediction[:cat_delimiter_ind]
            # categorical_var = get_var_from_list(categorical_var_name, vars)

            # LHS is categorical
            if cat_delimiter_ind < num_delimiter_ind:
                lhs = categorical_var_name.strip()
                category = lhs[cat_delimiter_ind + 1:num_delimiter_ind]
                lhs_var = get_var_from_list(lhs, vars)
                assert (lhs_var.category_exists(category))
                rhs = prediction[num_delimiter_ind + 1:].strip()
            else:
                assert (cat_delimiter_ind > num_delimiter_ind)
                lhs = prediction[:num_delimiter_ind].strip()
                rhs = prediction[num_delimiter_ind + 1:cat_delimiter_ind].strip()
                category = rhs[cat_delimiter_ind + 1:].strip()
                rhs_var = get_var_from_list(rhs, vars)
                assert (rhs_var.category_exists(category))

        # Prediction does not include categorical variable value (can still have a categorical variable)
        else:
            delimiter_ind = prediction.index(continuous_prediction_delimiter)
            lhs = prediction[:delimiter_ind].strip()
            rhs = prediction[delimiter_ind + 1:].strip()

        if continuous_negative_relationship in lhs:
            lhs = lhs[lhs.index(continuous_negative_relationship) + 1:].strip()
        elif continuous_positive_relationship in lhs:
            lhs = lhs[lhs.index(continuous_negative_relationship) + 1:].strip()
        else:
            pass

        if continuous_negative_relationship in rhs:
            rhs = rhs[rhs.index(continuous_negative_relationship) + 1:].strip()
        elif continuous_positive_relationship in rhs:
            rhs = rhs[rhs.index(continuous_positive_relationship) + 1:].strip()
        else:
            pass

        return get_var_from_list(lhs, vars) and get_var_from_list(rhs, vars)
    else:
        raise ValueError(f"Malformed prediction. Is neither categorical nor numeric:{prediction}")


def create_prediction(prediction_type: str, vars: list, prediction: str):
    global categorical_prediction, categorical_prediction_delimiter, categorical_comparators
    global continuous_prediction, continuous_prediction_delimiter, positive_relationship, negative_relationship

    if categorical_prediction == prediction_type:
        # comparator = None

        for c in categorical_comparators:
            if c in prediction:
                delimiter_ind = prediction.index(categorical_prediction_delimiter)
                comparator_ind = prediction.index(c)

                var_name = prediction[:delimiter_ind].strip()
                var = get_var_from_list(var_name, vars)
                lhs = prediction[delimiter_ind + 1:comparator_ind].strip()
                # Add len(c) to index in case comparator is longer than one character
                rhs = prediction[comparator_ind + len(c):].strip()

                types = set(type(k) for k in var.categories.keys())
                assert (len(types) == 1)  # Assert all keys have the same type
                cat_type = next(iter(types))

                if isinstance(lhs, str) and cat_type == int:
                    lhs = int(lhs)
                    rhs = int(rhs)

                assert (lhs in var.categories.keys())
                assert (rhs in var.categories.keys())
                if c == '<':
                    return [const(lhs) < const(rhs)]
                elif c == '>':
                    return [const(lhs) > const(rhs)]
                elif c == '==':
                    return [const(lhs) == const(rhs)]
                else:
                    assert (c == '!=')
                    return [const(lhs) != const(rhs)]
    else:
        assert (continuous_prediction == prediction_type)

        # Prediction includes categorical variable value
        if categorical_prediction_delimiter in prediction:
            cat_delimiter_ind = prediction.index(categorical_prediction_delimiter)
            num_delimiter_ind = prediction.index(continuous_prediction_delimiter)

            categorical_var_name = prediction[:cat_delimiter_ind]
            # categorical_var = get_var_from_list(categorical_var_name, vars)

            # LHS is categorical
            if cat_delimiter_ind < num_delimiter_ind:
                lhs = categorical_var_name.strip()
                rhs = prediction[num_delimiter_ind + 1:].strip()
            else:
                assert (cat_delimiter_ind > num_delimiter_ind)
                lhs = prediction[:num_delimiter_ind].strip()
                rhs = prediction[num_delimiter_ind + 1:cat_delimiter_ind].strip()

        # Prediction does not include categorical variable value (can still have a categorical variable)
        else:
            delimiter_ind = prediction.index(continuous_prediction_delimiter)
            lhs = prediction[:delimiter_ind].strip()
            rhs = prediction[delimiter_ind + 1:].strip()

            lhs_dir = '+'  # Positive relationship/change in variable is the default
            rhs_dir = '+'  # Positive relationship/change in variable is the default

            if lhs.startswith(continuous_negative_relationship) or lhs.startswith(continuous_positive_relationship):  # "as LHS decreases,..."
                lhs_dir = lhs[0]
                lhs = lhs[1:]
                lhs_var = get_var_from_list(lhs, vars)
            else:
                # do nothing to lhs, lhs_dir
                lhs_var = get_var_from_list(lhs, vars)

            if rhs.startswith(continuous_negative_relationship) or rhs.startswith(continuous_positive_relationship):
                rhs_dir = rhs[0]
                rhs = rhs[1:]
                rhs_var = get_var_from_list(rhs, vars)
            else:
                # do nothing to rhs, rhs_dir
                rhs_var = get_var_from_list(rhs, vars)

            if lhs_dir == rhs_dir:  # handles +lhs, +rhs and -lhs,
                return Relationship(lhs_var).positive(Relationship(rhs_var))
            else:  # handles +lhs, -rhs and -lhs, +rhs
                return Relationship(lhs_var).negative(Relationship(rhs_var))


# def predict(factors: list, outcome: Variable, prediction: str=None):
def predict(vars: list, predictions: list = None):
    formulated_predictions = []

    # Validate well-formedness of predictions
    if predictions:
        # Check that each prediction is well-formed
        for p in predictions:
            assert (isinstance(p, str))
            # Does the prediction pertain to categorical data?
            if categorical_prediction_delimiter in p and continuous_prediction_delimiter not in p:
                assert (is_well_formed_prediction(categorical_prediction, vars, p))
                pred = create_prediction(categorical_prediction, vars, p)

            # Does the prediction pertain to numerical data?
            elif continuous_prediction_delimiter in p:
                assert (is_well_formed_prediction(continuous_prediction, vars, p))
                # import pdb; pdb.set_trace()
                pred = create_prediction(continuous_prediction, vars, p)

            # Prediction pertains to neither categorical nor numerical data                 
            else:
                raise ValueError(f"Prediction is malformed: {p}")

            formulated_predictions.append(pred)

    return formulated_predictions


# Generic interface for observing relationships among variables (observational studies and experiments)
# @params: vars should be a list of Variables
def relate(vars: list, prediction: list = None):
    return Relate(vars, predict(vars, prediction))


# @params: iv could be the list of variables/groups want to compare on dv -
# may only want to compare 2 groups, not all conditions
# def compare(var_1: Variable, var_2: Variable, prediction: str=None, when: str=None) :

# def compare(iv: Variable, dv: Variable, prediction: str=None, when: str=None) :
def compare(vars: list, prediction: list = None, when: str = None):
    return Relate(vars, predict(vars, prediction))

    # if (isinstance(iv, Variable)):
    #     vars = [(iv, iv_identifier), (dv, dv_identifier)]
    #     if isnominal(iv) or isordinal(iv):
    #         return Relate(vars, predict(vars, prediction))
    #     elif isnumeric(iv):
    #         return Relate(vars, predict(vars, prediction))
    #     else: 
    #         raise ValueError(f"Invalid Variable type: {iv.dtype}")
    # elif (isinstance(iv, list)): 
    #     vars = []
    #     for i in iv: 
    #         vars.append((i, iv_identifier))
    #     return Relate(vars, predict(vars, prediction))
    # else: 
    #     raise ValueError (f"IV (first parameter) is not a Variable or list of Variables: {f.type}")

# def compare(var, var, semantically_same=True): # Compare two groups
#     pass

# compare(iv, dv, predictions)
# compare(dv, dv, groups=False) or compare (iv, iv, groups=False) 
# # Are they the same groups? 

# strategy = nominal('strategy', ['forking', 'caching', 'naive'])
# ratio('time', drange=[0, 10000], comes_from=(strategy, ['forking', 'caching', 'naive']))
