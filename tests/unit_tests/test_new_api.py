import tea
from tea.runtimeDataStructures.variable import AbstractVariable, NominalVariable, OrdinalVariable, NumericVariable
from tea.runtimeDataStructures.design import AbstractDesign, ObservationalDesign, ExperimentDesign
from tea.runtimeDataStructures.hypothesis import PositiveLinear, NegativeLinear

import pandas as pd
import copy


def test_load_data_csv():

    file_path = "./datasets/UScrime.csv"

    df = pd.read_csv(file_path)

    data_obj = tea.data(file_path)

    assert df.equals(data_obj.data)


def test_load_data_df():
    file_path = "./datasets/UScrime.csv"

    df = pd.read_csv("./datasets/UScrime.csv")
    df2 = copy.deepcopy(df)

    data_obj = tea.data(df2)

    assert df.equals(data_obj.data)


def test_df_copy():
    file_path = "./datasets/UScrime.csv"

    df = pd.read_csv(file_path, encoding="utf-8")

    data_obj = tea.data(df)
    df = df.applymap(lambda x: x ** 2)  # square all elements

    assert df.equals(data_obj.data.applymap(lambda x: x ** 2))


def test_define_nominal_variable():
    categories = ["0", "1"]

    var = {"name": "So", "data type": "nominal", "categories": categories}

    vars = [var]

    vars_list = tea.define_variables(vars)
    var_0 = vars_list[0]
    assert isinstance(var_0, NominalVariable)
    assert var_0.categories == categories


def test_define_nominal_variable_extract_categories():
    categories = ["0", "1"]

    var = {"name": "So", "data type": "nominal"}

    vars = [var]

    vars_list = tea.define_variables(vars)
    var_0 = vars_list[0]
    assert isinstance(var_0, NominalVariable)
    assert var_0.categories == None


def test_define_ordinal_variable():
    var = {"name": "Grade", "data type": "ordinal", "categories": ["0", "1", "2"]}

    vars = [var]

    vars_list = tea.define_variables(vars)
    var_0 = vars_list[0]
    assert isinstance(var_0, OrdinalVariable)


def test_define_ordinal_variable_error():
    var = {"name": "Grade", "data type": "ordinal"}

    vars = [var]

    vars_list = None
    try:
        vars_list = tea.define_variables(vars)
    except:
        pass
    assert vars_list == None


def test_define_numeric_variable():
    var = {"name": "Prob", "data type": "numeric"}

    vars = [var]

    vars_list = tea.define_variables(vars)
    var_0 = vars_list[0]
    assert isinstance(var_0, NumericVariable)


def test_define_interval_variable():
    var = {"name": "Prob", "data type": "interval"}

    vars = [var]

    vars_list = tea.define_variables(vars)
    var_0 = vars_list[0]
    assert isinstance(var_0, NumericVariable)


def test_define_ratio_variable():
    var = {"name": "Prob", "data type": "ratio"}

    vars = [var]

    vars_list = tea.define_variables(vars)
    var_0 = vars_list[0]
    assert isinstance(var_0, NumericVariable)


def test_define_obs_study_x():
    var = {"name": "Grade", "data type": "ordinal", "categories": ["0", "1", "2"]}
    design = {"study type": "observational study", "contributor variable": "Grade"}

    vars = [var]

    vars_list = tea.define_variables(vars)
    design_obj = tea.define_study_design(design, vars_list)
    assert isinstance(design_obj, ObservationalDesign)
    assert isinstance(design_obj.xs, list)
    assert not "ys" in design_obj.__dict__
    assert vars_list[0] == design_obj.xs[0]


def test_define_obs_study_xs():
    var_0 = {"name": "Grade", "data type": "ordinal", "categories": ["0", "1", "2"]}
    var_1 = {"name": "So", "data type": "nominal", "categories": ["0", "1"]}
    design = {"study type": "observational study", "contributor variables": ["Grade", "So"]}

    vars = [var_0, var_1]

    vars_list = tea.define_variables(vars)
    design_obj = tea.define_study_design(design, vars_list)
    assert isinstance(design_obj, ObservationalDesign)
    assert isinstance(design_obj.xs, list)
    assert not "ys" in design_obj.__dict__
    assert vars_list == design_obj.xs


def test_define_obs_study_y():
    var = {"name": "Prob", "data type": "ratio"}
    design = {"study type": "observational study", "outcome variable": "Prob"}

    vars = [var]

    vars_list = tea.define_variables(vars)
    design_obj = tea.define_study_design(design, vars_list)
    assert isinstance(design_obj, ObservationalDesign)
    assert not "xs" in design_obj.__dict__
    assert isinstance(design_obj.ys, list)
    assert vars_list[0] == design_obj.ys[0]


def test_define_obs_study_ys():
    var_0 = {"name": "Prob", "data type": "ratio"}
    var_1 = {"name": "Income", "data type": "numeric"}
    design = {"study type": "observational study", "outcome variables": ["Prob", "Income"]}

    vars = [var_0, var_1]

    vars_list = tea.define_variables(vars)
    design_obj = tea.define_study_design(design, vars_list)
    assert isinstance(design_obj, ObservationalDesign)
    assert not "xs" in design_obj.__dict__
    assert isinstance(design_obj.ys, list)
    assert vars_list == design_obj.ys


def test_define_experiment_x():
    var = {"name": "Grade", "data type": "ordinal", "categories": ["0", "1", "2"]}
    design = {"study type": "experiment", "independent variable": "Grade"}

    vars = [var]

    vars_list = tea.define_variables(vars)
    design_obj = tea.define_study_design(design, vars_list)
    assert isinstance(design_obj, ExperimentDesign)
    assert isinstance(design_obj.xs, list)
    assert not "ys" in design_obj.__dict__
    assert vars_list[0] == design_obj.xs[0]


def test_define_experiment_xs():
    var_0 = {"name": "Grade", "data type": "ordinal", "categories": ["0", "1", "2"]}
    var_1 = {"name": "So", "data type": "nominal", "categories": ["0", "1"]}
    design = {"study type": "experiment", "independent variables": ["Grade", "So"]}

    vars = [var_0, var_1]

    vars_list = tea.define_variables(vars)
    design_obj = tea.define_study_design(design, vars_list)
    assert isinstance(design_obj, ExperimentDesign)
    assert isinstance(design_obj.xs, list)
    assert not "ys" in design_obj.__dict__
    assert vars_list == design_obj.xs


def test_define_experiment_y():
    var = {"name": "Prob", "data type": "ratio"}
    design = {"study type": "experiment", "dependent variable": "Prob"}

    vars = [var]

    vars_list = tea.define_variables(vars)
    design_obj = tea.define_study_design(design, vars_list)
    assert isinstance(design_obj, ExperimentDesign)
    assert not "xs" in design_obj.__dict__
    assert isinstance(design_obj.ys, list)
    assert vars_list[0] == design_obj.ys[0]


def test_define_experiment_ys():
    var_0 = {"name": "Prob", "data type": "ratio"}
    var_1 = {"name": "Income", "data type": "numeric"}
    design = {"study type": "experiment", "dependent variables": ["Prob", "Income"]}

    vars = [var_0, var_1]

    vars_list = tea.define_variables(vars)
    design_obj = tea.define_study_design(design, vars_list)
    assert isinstance(design_obj, ExperimentDesign)
    assert not "xs" in design_obj.__dict__
    assert isinstance(design_obj.ys, list)
    assert vars_list == design_obj.ys


def test_assume_ordinal_var():
    var = {"name": "Grade", "data type": "ordinal", "categories": ["0", "1", "2"]}
    prop_0 = "log normal"
    assumptions = {prop_0: "Grade"}

    vars = [var]
    vars_list = tea.define_variables(vars)
    tea.assume(assumptions, vars_list)
    assert vars_list[0].properties[0] == prop_0


def test_assume_numeric_var():
    var = {"name": "Prob", "data type": "ratio"}
    prop = "normally distributed"
    assumptions = {prop: "Prob"}

    vars = [var]
    vars_list = tea.define_variables(vars)
    tea.assume(assumptions, vars_list)
    assert vars_list[0].properties[0] == prop


def test_tea_ctor():
    INFER_MODE = "infer"
    file_path = "./datasets/UScrime.csv"
    var = {"name": "Grade", "data type": "ordinal", "categories": ["0", "1", "2"]}
    vars = [var]
    design = {"study type": "experiment", "independent variable": "Grade"}

    tea_obj = tea.Tea(vars, design)
    vars_list = tea.define_variables(vars)
    assert tea_obj.variables[0] == vars_list[0]
    design_obj = tea.define_study_design(design, vars_list)
    assert tea_obj.design == design_obj
    tea_obj.load_data(file_path)
    data_obj = tea.data(file_path)
    assert tea_obj.data == data_obj
    assert tea_obj.mode == INFER_MODE  # Would be better to use globals?


def test_tea_ctor_set_mode():
    INFER_MODE = "infer"
    STRICT_MODE = "strict"
    RELAXED_MODE = "relaxed"
    file_path = "./datasets/UScrime.csv"
    var = {"name": "Grade", "data type": "ordinal", "categories": ["0", "1", "2"]}
    vars = [var]
    design = {"study type": "experiment", "independent variable": "Grade"}

    tea_obj = tea.Tea(vars, design)
    vars_list = tea.define_variables(vars)
    assert tea_obj.variables[0] == vars_list[0]
    design_obj = tea.define_study_design(design, vars_list)
    assert tea_obj.design == design_obj
    tea_obj.load_data(file_path)
    data_obj = tea.data(file_path)
    assert tea_obj.data == data_obj
    # Check Default
    assert tea_obj.mode == INFER_MODE  # Would be better to use globals?
    tea_obj.set_mode(STRICT_MODE)
    assert tea_obj.mode == STRICT_MODE  # Would be better to use globals?
    tea_obj.set_mode(RELAXED_MODE)
    assert tea_obj.mode == RELAXED_MODE  # Would be better to use globals?


def test_assume_tea_obj():
    file_path = "./datasets/UScrime.csv"
    var = {"name": "Grade", "data type": "ordinal", "categories": ["0", "1", "2"]}
    vars = [var]
    design = {"study type": "experiment", "independent variable": "Grade"}
    prop = "normally distributed"
    assumptions = {prop: "Prob"}

    tea_obj = tea.Tea(vars, design)
    vars_list = tea.define_variables(vars)
    assert tea_obj.variables[0] == vars_list[0]
    design_obj = tea.define_study_design(design, vars_list)
    assert tea_obj.design == design_obj
    tea_obj.load_data(file_path)
    data_obj = tea.data(file_path)
    assert tea_obj.data == data_obj
    tea.assume(assumptions, vars_list)
    tea_obj.assume(assumptions)
    assert tea_obj.variables[0].properties == vars_list[0].properties


def test_linearHypothesis_malformed():
    var_0 = {"name": "Prob", "data type": "ratio"}
    var_1 = {"name": "So", "data type": "nominal", "categories": ["0", "1"]}
    design = {"study type": "experiment", "independent variables": "So", "dependent variable": "Prob"}

    vars = [var_0, var_1]
    tea_obj = tea.Tea(vars, design)
    vars_list = tea.define_variables(vars)
    design_obj = tea.define_study_design(design, vars_list)
    hypo_obj = None
    try:
        hypo_obj = tea_obj.hypothesize("+Prob~+So")
    except ValueError:
        assert hypo_obj is None


def test_linearHypothesis_pos_signed_ctor():
    var_0 = {"name": "Prob", "data type": "ratio"}
    var_1 = {"name": "Income", "data type": "numeric"}
    design = {"study type": "experiment", "independent variables": "Income", "dependent variable": "Prob"}

    vars = [var_0, var_1]
    tea_obj = tea.Tea(vars, design)
    vars_list = tea.define_variables(vars)
    design_obj = tea.define_study_design(design, vars_list)
    hypo_obj_0 = tea_obj.hypothesize("Income~Prob")

    assert isinstance(hypo_obj_0, PositiveLinear)
    assert vars_list[0] in design_obj.ys
    assert vars_list[1] in design_obj.xs
    assert hypo_obj_0.xs == design_obj.xs
    assert hypo_obj_0.y == design_obj.ys


def test_linearHypothesis_default_ctor():
    var_0 = {"name": "Prob", "data type": "ratio"}
    var_1 = {"name": "Income", "data type": "numeric"}
    design = {"study type": "experiment", "independent variables": "Income", "dependent variable": "Prob"}

    vars = [var_0, var_1]
    tea_obj = tea.Tea(vars, design)
    vars_list = tea.define_variables(vars)
    design_obj = tea.define_study_design(design, vars_list)
    hypo_obj_0 = tea_obj.hypothesize("Income~Prob")
    hypo_obj_1 = tea_obj.hypothesize("Income~+Prob")
    hypo_obj_2 = tea_obj.hypothesize("+Income~Prob")
    hypo_obj_3 = tea_obj.hypothesize("+Income~+Prob")

    assert hypo_obj_0 == hypo_obj_1 == hypo_obj_2 == hypo_obj_3


def test_linearHypothesis_neg_signed_ctor():
    var_0 = {"name": "Prob", "data type": "ratio"}
    var_1 = {"name": "Income", "data type": "numeric"}
    design = {"study type": "experiment", "independent variables": "Income", "dependent variable": "Prob"}

    vars = [var_0, var_1]
    tea_obj = tea.Tea(vars, design)
    vars_list = tea.define_variables(vars)
    design_obj = tea.define_study_design(design, vars_list)
    hypo_obj_0 = tea_obj.hypothesize("-Income~Prob")

    assert isinstance(hypo_obj, NegativeLinear)
    assert vars_list[0] in design_obj.ys
    assert vars_list[1] in design_obj.xs
    assert hypo_obj.xs == design_obj.xs
    assert hypo_obj.y == design_obj.ys


# def test_groupComparisons_ctor():
#     var_0 = {
#         'name': 'Prob',
#         'data type': 'ratio'
#     }
#     var_1 = {
#         'name': 'So',
#         'data type': 'nominal',
#         'categories': ['0', '1']
#     }
#     design = {
#         'study type': 'experiment',
#         'independent variables': 'So',
#         'dependent variable': 'Prob'
#     }

#     vars = [var_0, var_1]
#     tea_obj = tea.Tea(vars, design)
#     vars_list = tea.define_variables(vars)
#     design_obj = tea.define_study_design(design, vars_list)
#     hypo_obj = tea_obj.hypothesize("-Prob~+So")
#     assert(isinstance(hypo_obj, NegativeLinear))
#     assert(vars_list[0] in design_obj.ys)
#     assert(vars_list[1] in design_obj.xs)
#     assert(hypo_obj.xs == design_obj.xs)
#     assert(hypo_obj.y == design_obj.ys)

# FIRST FOCUS ON Y ~ X
# TODO: HOW about when X ~ X ??

# make test where so ~ grade == grade ~ so (does not matter which direction, as long as keep y on one side and x on the other side)

# for var in all_vars:
# >           assert(isinstance(var, AbstractVariable))

# TODO: may want to add a helper function to determine if two designs are equivalent
