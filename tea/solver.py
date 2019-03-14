import attr
# import z3
# from .global_vals import *
# from enum import Flag, auto
import z3
# from z3 import BoolVal, Bool, Optimize, And, sat
from tea.evaluate_data_structures import VarData, CombinedData, BivariateData, MultivariateData
from tea.evaluate_data_structures import is_continuous_or_ordinal
from tea.global_vals import *
from typing import Dict, List

# Prog -> List[StatisticalTest] -> Query

# Contains a map from z3 variables representing tests
# back to the test objects allowing us to map back
# from a model back to the tests.
__test_map__ = {}

#  A list of all tests in the system which we can use
# to iterate over all tests.
__ALL_TESTS__ = []

def all_tests():
    """A helper for accessing the global set of tests"""
    global __ALL_TESTS__
    return __ALL_TESTS__


# Contains the global map from z3 variables which
# represent properties applied to variables back
# the properties that were applied.
__property_var_map__ = {}

# Contains a map from z3 variables representing the props
# back to the Property objects
__property_map__ = {}

# List of all Properties in the system which we can use 
# to iterate over all properties 
__ALL_PROPERTIES__ = []

# Map of all properties to functions that
# will give values to the properties
__property_to_function__ = {}

def all_props(): 
    """A helper for accessing the global set of properties"""
    global __ALL_PROPERTIES__
    return __ALL_PROPERTIES__

def subset_props(scope): 
    """A helper for accessing subset of properties based on their scope (Test or variable, for now)"""
    props = all_props()
    selected_props = []
    for p in props: 
        if p.scope == scope:
            selected_props.append(p)

    return selected_props

@attr.s(hash=False, cmp=False, auto_attribs=True, init=False)
class StatVar:
    name: str

    def __init__(self, name):
        self.name = name
        self.__z3__ = z3.Bool(self.name)


# TODO write test that these areq unique with pointer eq
# i.e StatVar('x') != StatVar('x')
# vs
# x = StatVar('x')
# assert x == x

class StatisticalTest:
    name: str
    variables: List[StatVar]
    test_properties: List["Property"]

    # properties_for_vars maps from a property to lists of indices
    # into test_vars that the property applies to. If the property
    # has arity 1, then it maps to a list of lists of length 1.
    # Similarly, if the property has arity 2, then it maps to
    # a list of lists of length 2.
    properties_for_vars: Dict["Property", List[List[int]]]

    # This needs to store number of variables
    # each property needs to be mapped to variable
    # 
    # effectives 
    # 
    # Test("foo", 
    #   test_vars=[v1, v2], 
    #   test_props=[p5],
    #   properties_for_vars={ p1: v1, p2: v2, p3: v3 }])
    # 
    def __init__(self, name, test_vars, test_properties=None, properties_for_vars=None):
        global __test_map__, __ALL_TESTS__
        self.name = name
        self.test_vars = test_vars

        if test_properties is None:
            test_properties = []

        if properties_for_vars is None:
            properties_for_vars = {}

        self.test_properties = test_properties

        self.properties_for_vars = {}
        for key in properties_for_vars:
            # properties_for_vars is a list of lists of variables. Get the indices of the variables
            # in each list.
            for args in properties_for_vars[key]:
                indices = [self.test_vars.index(arg) for arg in args]
                if key not in self.properties_for_vars.keys():
                    self.properties_for_vars[key] = []
                self.properties_for_vars[key].append(indices)

        # Create variable.
        self.__z3__ = z3.Bool(self.name)

        # Populate global table.
        __test_map__[self.__z3__] = self
        __ALL_TESTS__.append(self)

    # Question: does this mean you can't consider two tests of the same type on different variables at once?
    def apply(self, *test_vars):
        assert len(test_vars) == len(self.test_vars)
        self.test_vars = test_vars

    def _populate_properties(self):
        # Populate all props
        self._properties = []
        for prop in self.test_properties:
            # This is weird, and doesn't really fit into property model
            self._properties.append(prop(StatVar(self.name)))

        for prop in self.properties_for_vars:
            list_of_variable_indices = self.properties_for_vars[prop]
            for variable_indices in list_of_variable_indices:
                variable_indices = [self.test_vars[i] for i in variable_indices]
                # import pdb; pdb.set_trace()
                self._properties.append(prop(*variable_indices))

    def query(self):  # May want to change this....
        self._populate_properties()  # Apply to specific instance of variables
        # if self.__query__ is None:
        conj = []
        for p in self._properties:  # combines Test and Var-specific properties
            # p.__z3__ = uninterpreted function
            # p.__var__ = instantiated z3 BoolVal
            # Add the uf, and interpret the uf as always ==ing the instantiated BoolVal
            # conj += [p.__z3__, p.__z3__ == p.__var__]
            conj += [p.__z3__]

        return conj
        # self.__query__ = query
        # return self.__query__

    @staticmethod
    def get_by_z3_var(var):
        """
        This relationship holds:
            t1 == StatisticalTet.get_by_z3_var(t1.__var__)
        """
        global __test_map__
        return __test_map__.get(var)


class Property:
    name: str
    description: str
    arity: int

    def __init__(self, name, description, scope, arity=1):
        global __property_map__, __ALL_PROPERTIES__

        self.name = name
        self.description = description
        if scope == 'test' or scope == 'variable': 
            self.scope = scope
        else: 
            raise ValueError(f"Either TEST or VARIABLE is possible, but received {scope}")
        self.arity = arity
        args = []
        for _ in range(self.arity):
            args.append(z3.BoolSort())
        args.append(z3.BoolSort())
        self.__z3__ = z3.Function(self.name, *args)  # e.g. continuous(x)
        self.__cache__ = {}

        # Populate global table.    
        __property_map__[self.__z3__] = self
        __ALL_PROPERTIES__.append(self)

    def __str__(self):
        return f"property:{self.name}"

    def __repr__(self):
        return f"Property({self.name})"

    def __call__(self, *var_names):
        if len(var_names) != self.arity:
            raise Exception(f"{self.name} property has arity {self.arity} " \
                            f"found {len(var_names)} arguments")
        cached = self.__cache__.get(tuple(var_names))
        if cached:
            return cached
        
        ap = AppliedProperty(self, var_names)
        # self.__cache__[tuple(var_names)] = ap
        return ap

    def reset(self):
        args = []
        for _ in range(self.arity):
            args.append(z3.BoolSort())
        args.append(z3.BoolSort())
        self.__z3__ = z3.Function(self.name, *args)  # e.g. continuous(x)


class AppliedProperty:
    property: Property

    def __init__(self, prop, test_vars):
        global __property_var_map__
        self.property = prop  # e.g. continuous
        self.test_vars = test_vars  # (StatVar(name='x'),)
        # self._name = ""
        z3_args = []
        for tv in test_vars:
            # Allows for unique identification of prop -> var, but not looking up from model because that refs prop name
            # self._name += tv.name + ":"
            # self._name + tv.name
            z3_args.append(tv.__z3__)
        self._name = self.property.name  # continuous
        # Why is property fn a bool? Does this allow continuous(x) and not continuous(y)?
        # Answer: I think the undefined function is able to capture all functionality of
        # deciding the boolean property value for each variable, so the z3.Bool() for the
        # property name isn't necessary.
        # self.__var__ = z3.Bool(self._name)  # e.g. continuous
        self.__z3__ = prop.__z3__(*z3_args)  # e.g. continuous(x)

        # _name needs to be unique to avoid overwriting same property for different variables.
        # But if it is unique, it makes it more difficult to look up from the z3 model.
        # Solution: Make the name the same, but have it map to a list of variables that the
        # property applies to.
        if self._name not in __property_var_map__.keys():
            __property_var_map__[self._name] = []

        # TODO: When does __property_var_map__ need to be cleared?
        __property_var_map__[self._name].append(test_vars)

    def __str__(self):
        return f"property_for_var:{self._name}"

    def __repr__(self):
        return f"AppliedProperty({self._name})"

    @staticmethod
    def get_by_z3_var(name):
        global __property_var_map__
        return __property_var_map__.get(name)


# Test properties
one_x_variable = Property('has_one_x', "Exactly one explanatory variable", 'test')
one_y_variable = Property('has_one_y', "Exactly one explained variable", 'test')
paired = Property('has_paired_observations', "Paired observations", 'test')
independent = Property('has_independent_observations', "Independent (not paired) observations", 'test')
# not_paired = Property('not_paired', "Paired observations", 'test')

# Variable properties
categorical = Property('is_categorical', "Variable is categorical", 'variable')
two_categories = Property('has_two_categories', "Variable has two categories", 'variable')
# all_x_variables_categorical = Property('has_all_x_categorical', "All explanatory variables are categorical", 'variable')
# two_x_variable_categories = Property('has_two_categories_x_var', "Exactly two categories in explanatory variable", 'variable')
continuous = Property('is_continuous', "Continuous (not categorical) data", 'variable')
# We could create a disjunction of continuous \/ ordinal instead
continuous_or_ordinal = Property('is_continuous_or_ordinal', "Continuous OR ORDINAL (not nominal) data", 'variable')
normal = Property('is_normal', "Normal distribution", 'variable')
eq_variance = Property('has_equal_variance', "Equal variance", 'test')

two_categories_eq_variance = Property('two_cat_eq_var', "Two groups have equal variance", 'variable', 2)

# def has_one_x_variable(combined_data: CombinedData): 
#     pass

# def all_x_variables_categorical(combined_data: CombinedData): 
#     pass
# Map properties to functions
# __property_to_function__[one_x_variable] = has_one_x_variable
# __property_to_function__[all_x_variables_categorical] = all_x_variables_categorical

# one_x_variable = Property('one_x', "Exactly one explanatory variable")  # test property
# all_x_variables_categorical = Property('all_x_cat', "All explanatory variables are categorical")
# two_x_variable_categories = Property('two_x_var', "Exactly two categories in explanatory variable")
# one_y_variable = Property('one_y_var', "Exactly one explained variable")  # test property

# categorical = Property('categorical', "Categorical (not continuous) data")
# continuous = Property('continuous', "Continuous (not categorical) data")
# normal = Property('normal', "Normal distribution")
# paired = Property('paired', "Paired observations")  # test property
# eq_variance = Property('equal_var', "Equal variance", 2)

# two_categories_eq_variance = Property('two_cat_eq_var', "Two groups have equal variance", 2)


def construct_axioms(variables):  # List[StatVar]
    _axioms = []
    for var in variables:
        # A variable must be continuous or categorical, but not both.
        _axioms.append(z3.And(z3.Or(continuous(var).__z3__, categorical(var).__z3__),
                              z3.Not(z3.And(continuous(var).__z3__, categorical(var).__z3__))))

        # If a variable is an explanatory variable and all explanatory variables are categorical,
        # then the variable must be categorical.
        # It isn't clear how to reason about whether a variable is an explanatory or explained variable.
        # _axioms.append(z3.Implies(all_x_variables_categorical(var).__z3__, categorical(var).__z3__))

        # Not sure how to reason about test properties like one_x_variable and one_y_variable.
        # _axioms.append(z3.Not(z3.And(one_x_variable(var).__z3__, one_y_variable(var).__z3__)))

        # If a variable is normal, then it cannot be categorical.
        _axioms.append(z3.Implies(normal(var).__z3__, z3.Not(categorical(var).__z3__)))

        # If a variable has two categories, then it must be categorical.
        # _axioms.append(z3.Implies(two_x_variable_categories(var).__z3__, categorical(var).__z3__))

    return _axioms


x = StatVar('x')
y = StatVar('y')

students_t = StatisticalTest('students_t', [x, y],
                            test_properties=
                                [one_x_variable, one_y_variable, independent, eq_variance],
                            properties_for_vars={
                                  categorical : [[x]],
                                  two_categories: [[x]],
                                  continuous: [[y]],
                                  normal: [[y]],
                                #   eq_variance: [x, y] # Not sure about this
                                })

welchs_t = StatisticalTest('welchs_t', [x, y],
                            test_properties=
                                [one_x_variable, one_y_variable, independent],
                            properties_for_vars={
                                  categorical : [[x]],
                                  two_categories: [[x]],
                                  continuous: [[y]],
                                  normal: [[y]],
                                })

mannwhitney_u = StatisticalTest('mannwhitney_u', [x, y],
                            test_properties=
                                [one_x_variable, one_y_variable, independent],
                            properties_for_vars={
                                  categorical : [[x]],
                                  two_categories: [[x]],
                                  continuous_or_ordinal: [[y]],
                                # conflicting sources, but remove for now
                                #   eq_variance: [x, y] # Is this an assumption of mann whitney??
                                })                                

# Specify variable properties as list of lists so that the same property can
# apply to multiple variables individually. If "categorical" is specified twice,
# only the second variable is kept because it overwrites the first entry in the
# dictionary.
chi_square_test = StatisticalTest('chi_square', [x, y],
                                   test_properties=[one_x_variable, one_y_variable],
                                   properties_for_vars={
                                       categorical: [[x], [y]]
                                   })

z = StatVar('z')
w = StatVar('w')
students_t.apply(z, w)
mannwhitney_u.apply(z, w)
chi_square_test.apply(z, w)

axioms = construct_axioms([z, w])

# Problem statement: Given a set of properties, tell me which tests are valid to run
# This is a concrete (rather than symbolic) problem 
# @param combined_data CombinedData object
# @returns list of Property objects that combined_data exhibits
def which_tests(combined_data:CombinedData):
    
    valid_tests_names = []

    # Apply all test properties
    for prop in subset_props('test'): 
        prop_val = getattr(CombinedData,prop.name)(combined_data)
        prop.__z3__ = z3.BoolVal(prop_val)

    for test in all_tests(): 
        pass_all_test_props = True
        # check all test_properties first
        for prop in test.test_properties: 
            # If any test property is False, stop checking
            # the remaining test properties
            if prop.__z3__ == z3.BoolVal(False): 
                pass_all_test_props = False
                break
            # prop.reset()

        # Check variable properties only if all test properties pass
        # If the test properties don't all pass, the test does not apply
        if pass_all_test_props:
            print(f"\nPassed test-level properties for {test.name}...")
            is_valid_test = True
            # Assume that last variable in test.test_vars is the dependent variable (y)
            combined_data._update_vars() # reorder variables so that y var is at the end

            # Compile VarData to StatVar
            stat_vars = []
            data_vars = combined_data.vars
            for var in data_vars:
                stat_vars.append(StatVar(var.metadata[name]))
            
            test.apply(*stat_vars) # Apply test to variables

            var_props = test.properties_for_vars
            for prop, list_indices in var_props.items():
                for indices in list_indices:
                    # check the prop on the variable that corresponds to the index
                    var_data = []
                    for i in indices: 
                        var_data.append(data_vars[i])
                    try:
                        prop_val = getattr(VarData,prop.name)(*var_data)
                    except AttributeError:
                        prop_val = globals()[prop.name](*var_data)
                        prop.__z3__ = z3.BoolVal(prop_val)
                
                if not prop_val:
                    # import pdb; pdb.set_trace()
                    is_valid_test = False
                    print(f"...but did not have variable property: {prop.name}")
                    break
            
            if (is_valid_test):
                print(f"...and all variable properties!")
                valid_tests_names.append(test.name)
    
    # Reset all properties
    for p in all_props():
        p.reset()

    return valid_tests_names


def which_props(tests_names: list):
    tests = []

    for name in tests_names:
        for test in all_tests():
            if test.name == name:
                test._populate_properties() 
                tests.append(test)

    test_queries = []
    hard_constraints = []
    for test in tests:
        # The Bool representing whether the test can be run with the given property
        # values is a hard constraint because we want to satisfy all tests, but may
        # not be able to.
        hard_constraints.append(test.__z3__)

        # The relationship of the properties of variables required to run a specific
        # test is an axiom and cannot be violated.
        axioms.append(test.__z3__ == z3.And(*test.query()))

        # test_queries contains the individual property constraints (e.g. continuous(x)).
        # These will all be soft constraints with low weight because they may need to be
        # violated.
        test_queries += test.query()

    s = z3.Optimize()

    # Set weight of tests to large number so they are satisfied over properties.
    print("\nHard constraints:")
    for constraint in hard_constraints:
        print(constraint)
        s.add_soft(constraint, 1000)

    # Prefer to violate properties by giving them low weight.
    print("\nSoft constraints:")
    for soft_constraint in test_queries:
        print(soft_constraint)
        s.add_soft(soft_constraint, 1)

    # Axioms cannot be violated.
    print("\nAxioms:")
    for axiom in axioms:
        print(axiom)
        s.add(axiom)

    result = s.check()
    if result == z3.unsat:
        print("no solution")
    elif result == z3.unknown:
        print("failed to solve")
        try:
            print(s.model())
        except z3.Z3Exception:
            return
    else:
        model = s.model()
        _tests_and_properties = {}
        _test_to_broken_properties = {}
        for test in tests:
            test_name = test.name
            _tests_and_properties[test_name] = {}
            _test_to_broken_properties[test_name] = []

            # TODO: Unprotect test._properties.
            for test_property in test._properties:
                print("property: %s" % test_property)
                property_identifier = test_property._name
                for test_var in test_property.test_vars:
                    property_identifier += "_%s" % test_var.name
                property_result = bool(model.evaluate(test_property.__z3__))
                _tests_and_properties[test_name][property_identifier] = property_result
                if not property_result:
                    _test_to_broken_properties[test_name].append(property_identifier)

        import pdb; pdb.set_trace()
        return _tests_and_properties, _test_to_broken_properties


# test_to_properties, test_to_broken_properties = which_props([chi_square_test, students_t])

# print(ps)
# print("\nFound properties:")
# print(test_to_properties)
# print("\nProperties that could not be satisfied:")
# print(test_to_broken_properties)
# If properties do not hold, need to go back to solver with partially concrete assertions
# Use user assumptions to drive verification
