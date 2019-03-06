from tea.solver import get_independent_variable, get_dependent_variable, independent_variable_is_categorical,\
    independent_variable_is_continuous, independent_variable_has_number_of_categories, dependent_variable_is_continuous,\
    dependent_variable_is_categorical, dependent_variable_has_number_of_categories, dependent_variable_is_ordinal,\
    all_variables_have_enough_categories, all_variables_have_enough_samples, all_variables_are_continuous_or_ordinal,\
    all_variables_are_normal
from tea.evaluate_helper_methods import distribution, variance, sample_size, num_categories, data_type, iv_identifier, dv_identifier, null_identifier
from tea.evaluate_data_structures import CombinedData, VarData
from tea.ast import DataType

# Set up.
normal_continuous_properties = {
    distribution: 0.96,
    variance: 0.05,
    sample_size: 35,
}
categorical_properties = {
    sample_size: 35,
    num_categories: 2,
}

normal_continuous_metadata = {data_type: DataType.INTERVAL}
nominal_metadata = {data_type: DataType.NOMINAL}
ordinal_metadata = {data_type: DataType.ORDINAL}

normal_continuous_var = VarData(metadata=normal_continuous_metadata,
                                properties=normal_continuous_properties,
                                role=null_identifier)
normal_continuous_dependent = VarData(metadata=normal_continuous_metadata,
                                      properties=normal_continuous_properties,
                                      role=dv_identifier)
normal_continuous_independent = VarData(metadata=normal_continuous_metadata,
                                        properties=normal_continuous_properties,
                                        role=iv_identifier)
nominal_independent = VarData(metadata=nominal_metadata,
                              properties=categorical_properties,
                              role=iv_identifier)
ordinal_independent = VarData(metadata=ordinal_metadata,
                              properties=categorical_properties,
                              role=iv_identifier)
nominal_dependent = VarData(metadata=nominal_metadata,
                            properties=categorical_properties,
                            role=dv_identifier)
ordinal_dependent = VarData(metadata=ordinal_metadata,
                            properties=categorical_properties,
                            role=dv_identifier)
ordinal_var = VarData(metadata=ordinal_metadata,
                      properties=categorical_properties,
                      role=null_identifier)
nominal_var = VarData(metadata=nominal_metadata,
                      properties=categorical_properties,
                      role=null_identifier)

cont_not_specified = CombinedData(vars=[normal_continuous_var, normal_continuous_var])
cont_iv_dv = CombinedData(vars=[normal_continuous_dependent, normal_continuous_independent])
nominal_iv_cont_dv = CombinedData(vars=[normal_continuous_dependent, nominal_independent])
ordinal_iv_cont_dv = CombinedData(vars=[normal_continuous_dependent, ordinal_independent])
cont_iv_nominal_dv = CombinedData(vars=[nominal_dependent, normal_continuous_independent])
cont_iv_ordinal_dv = CombinedData(vars=[ordinal_dependent, normal_continuous_independent])
ordinal_not_specified = CombinedData(vars=[ordinal_var, ordinal_var])
nominal_not_specified = CombinedData(vars=[nominal_var, nominal_var])
ordinal_nominal_not_specified = CombinedData(vars=[ordinal_var, nominal_var])

def test_get_dv_and_iv():
    # Check that getting independent/dependent var fails if none is specified.
    assert get_dependent_variable(cont_not_specified) is None
    assert get_independent_variable(cont_not_specified) is None
    assert get_dependent_variable(cont_iv_dv) == normal_continuous_dependent
    assert get_independent_variable(cont_iv_dv) == normal_continuous_independent

def test_iv_properties():
    # Check all of methods on independent variable.
    assert independent_variable_is_continuous(cont_iv_dv)
    assert not independent_variable_is_continuous(nominal_iv_cont_dv)
    assert not independent_variable_is_continuous(ordinal_iv_cont_dv)

    assert not independent_variable_is_categorical(cont_iv_dv)
    assert independent_variable_is_categorical(nominal_iv_cont_dv)
    assert independent_variable_is_categorical(ordinal_iv_cont_dv)

    assert independent_variable_has_number_of_categories(nominal_iv_cont_dv, 2)
    assert not independent_variable_has_number_of_categories(nominal_iv_cont_dv, 0)
    assert not independent_variable_has_number_of_categories(nominal_iv_cont_dv, 3)

    assert independent_variable_has_number_of_categories(ordinal_iv_cont_dv, 2)
    assert not independent_variable_has_number_of_categories(ordinal_iv_cont_dv, 0)
    assert not independent_variable_has_number_of_categories(ordinal_iv_cont_dv, 3)

def test_dv_properties():
    # Check all methods on dependent variable.
    assert dependent_variable_is_continuous(cont_iv_dv)
    assert not dependent_variable_is_continuous(cont_iv_nominal_dv)
    assert not dependent_variable_is_continuous(cont_iv_ordinal_dv)

    assert not dependent_variable_is_categorical(cont_iv_dv)
    assert dependent_variable_is_categorical(cont_iv_nominal_dv)
    assert dependent_variable_is_categorical(cont_iv_ordinal_dv)

    assert dependent_variable_has_number_of_categories(cont_iv_nominal_dv, 2)
    assert not dependent_variable_has_number_of_categories(cont_iv_nominal_dv, 0)
    assert not dependent_variable_has_number_of_categories(cont_iv_nominal_dv, 3)

    assert dependent_variable_has_number_of_categories(cont_iv_ordinal_dv, 2)
    assert not dependent_variable_has_number_of_categories(cont_iv_ordinal_dv, 0)
    assert not dependent_variable_has_number_of_categories(cont_iv_ordinal_dv, 3)

    assert not dependent_variable_is_ordinal(cont_iv_dv)
    assert not dependent_variable_is_ordinal(cont_iv_nominal_dv)
    assert dependent_variable_is_ordinal(cont_iv_ordinal_dv)

def test_all_variables_methods():
    # Test all_variables_... methods.
    assert all_variables_are_normal(cont_iv_dv)
    assert all_variables_are_normal(cont_not_specified)
    assert not all_variables_are_normal(cont_iv_nominal_dv)
    assert not all_variables_are_normal(nominal_iv_cont_dv)

    assert all_variables_are_continuous_or_ordinal(cont_iv_dv)
    assert all_variables_are_continuous_or_ordinal(cont_iv_ordinal_dv)
    assert all_variables_are_continuous_or_ordinal(ordinal_iv_cont_dv)
    assert not all_variables_are_continuous_or_ordinal(cont_iv_nominal_dv)
    assert not all_variables_are_continuous_or_ordinal(nominal_iv_cont_dv)

    assert not all_variables_have_enough_categories(cont_iv_dv, 2)
    assert not all_variables_have_enough_categories(cont_iv_ordinal_dv, 2)
    assert not all_variables_have_enough_categories(ordinal_iv_cont_dv, 2)
    assert not all_variables_have_enough_categories(cont_iv_nominal_dv, 2)
    assert not all_variables_have_enough_categories(nominal_iv_cont_dv, 2)
    assert all_variables_have_enough_categories(ordinal_not_specified, 2)
    assert all_variables_have_enough_categories(nominal_not_specified, 2)
    assert all_variables_have_enough_categories(ordinal_nominal_not_specified, 2)
    assert not all_variables_have_enough_categories(ordinal_not_specified, 3)
    assert not all_variables_have_enough_categories(nominal_not_specified, 3)
    assert not all_variables_have_enough_categories(ordinal_nominal_not_specified, 3)

    assert all_variables_have_enough_samples(cont_iv_dv)
    assert all_variables_have_enough_samples(cont_iv_ordinal_dv)
    assert all_variables_have_enough_samples(cont_iv_nominal_dv)
    assert all_variables_have_enough_samples(nominal_iv_cont_dv)
    assert all_variables_have_enough_samples(ordinal_iv_cont_dv)
    assert all_variables_have_enough_samples(ordinal_not_specified)
    assert all_variables_have_enough_samples(nominal_not_specified)
    assert all_variables_have_enough_samples(ordinal_nominal_not_specified)
    assert not all_variables_have_enough_samples(cont_iv_dv, 50)
    assert not all_variables_have_enough_samples(cont_iv_ordinal_dv, 50)
    assert not all_variables_have_enough_samples(cont_iv_nominal_dv, 50)
    assert not all_variables_have_enough_samples(nominal_iv_cont_dv, 50)
    assert not all_variables_have_enough_samples(ordinal_iv_cont_dv, 50)
    assert not all_variables_have_enough_samples(ordinal_not_specified, 50)
    assert not all_variables_have_enough_samples(nominal_not_specified, 50)
    assert not all_variables_have_enough_samples(ordinal_nominal_not_specified, 50)
