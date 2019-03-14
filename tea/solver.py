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
            vs = self.properties_for_vars[prop]
            vs = [self.test_vars[i] for i in vs]
            # import pdb; pdb.set_trace()
            self._properties.append(prop(*vs))

    def query(self): # May want to change this....
        self._populate_properties() # Apply to specific instance of variables
        # if self.__query__ is None:
        conj = []
        for p in self._properties: # combines Test and Var-specific properties
            # p.__z3__ = uninterpreted function
            # p.__var__ = instantiated z3 BoolVal
            # Add the uf, and interpret the uf as always ==ing the instantiated BoolVal
            conj += [p.__z3__, p.__z3__ == p.__var__]            
        conj = conj + [self.__z3__]
        query = z3.And(*conj)
        return query
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
        self.__z3__ = z3.Function(self.name, *args)
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

    # def __not__(self):
    #     return z3.Not(self.__z3__)

class AppliedProperty:
    property: Property

    def __init__(self, prop, test_vars):
        global __property_var_map__
        self.property = prop
        self.test_vars = test_vars
        self._name = ""
        z3_args = []
        for tv in test_vars:
            # self._name += tv.name + ":"
            self._name + tv.name
            z3_args.append(tv.__z3__)
        self._name = self._name + self.property.name 
        self.__var__ = z3.Bool(self._name)
        self.__z3__ = prop.__z3__(*z3_args)
        __property_var_map__[self._name] = self

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
eq_variance = Property('has_equal_variance', "Equal variance", 'test', 2)

two_categories_eq_variance = Property('two_cat_eq_var', "Two groups have equal variance", 'variable', 2)

# def has_one_x_variable(combined_data: CombinedData): 
#     pass

# def all_x_variables_categorical(combined_data: CombinedData): 
#     pass
# Map properties to functions
# __property_to_function__[one_x_variable] = has_one_x_variable
# __property_to_function__[all_x_variables_categorical] = all_x_variables_categorical

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
z = StatVar('z')
w = StatVar('w')
students_t.apply(z, w)



## EUNICE
## TODO: FINISH WHICH TESTS -- flushed out a little bit, what isn't working
## TODO: START PAPER
# If property is a negation of another property, would like to know (e.g., normal and not normal)
# -- could use function not()

# Problem statement: Given a set of properties, tell me which tests are valid to run
# This is a concrete (rather than symbolic) problem 
# @param combined_data CombinedData object
# @returns list of Property objects that combined_data exhibits
def which_tests(combined_data:CombinedData):
    valid_tests = []

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

        # Check variable properties only if all test properties pass
        # If the test properties don't all pass, the test does not apply
        if pass_all_test_props:
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
                
                if prop.__z3__ == z3.BoolVal(False):
                    # import pdb; pdb.set_trace()
                    is_valid_test = False
                    break
            
            if (is_valid_test):
                import pdb; pdb.set_trace()
                valid_tests.append(test)
    
    return valid_tests

# def which_tests(props: list):
#     # comes from CombinedData, assumptions, and design 
    
#     for prop in props:
#         # for each prop p_N it becomes:
#         # query /\ p_n = True 
#         s.add(prop.__z3__ == z3.BoolVal(True))
    
#     for test in all_tests():
#         # query = query /\ test.query()
#         s.add(test.query())
    
#     result = s.check()
#     if result == z3.unsat:
#         print("no solution")
#     elif result == z3.unknown:
#         print("failed to solve")
#         try:
#             print(s.model())
#         except z3.Z3Exception:
#             return
#     else:
#         import pdb; pdb.set_trace()


def which_props(tests: list):
    test_queries = []
    for test in tests:
        test_queries.append(test.__z3__ == z3.BoolVal(True))
        test_queries.append(test.query())
    query = z3.And(test_queries) # May want to change
    # import pdb; pdb.set_trace()
    s = z3.Solver()
    s.add(query)
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
        props = []
        for decl in model.decls():
            prop = AppliedProperty.get_by_z3_var(decl.name())
            # import pdb; pdb.set_trace()
            if prop and model[decl] == True:
                props.append(prop)
            # else: 
                # import pdb; pdb.set_trace()
        return props


# ps = which_props([students_t])

# ts = which_tests(test_properties=[ 
#                  one_x_variable(students_t), 
#                  one_y_variable(students_t), 
#                  paired(students_t)],
#                             properties_for_vars={ all_x_variables_categorical : [x],
#                                   two_x_variable_categories: [x],
#                                   continuous: [y],
#                                   normal: [y],
#                                   eq_variance: [x, y]
#                                 })
# import pdb; pdb.set_trace()

# print(ps)
# If properties do not hold, need to go back to solver with partially concrete assertions
# Use user assumptions to drive verification
