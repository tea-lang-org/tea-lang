import attr
# import z3
# from .global_vals import *
from enum import Flag, auto
import z3
from z3 import BoolVal, Bool, Optimize, And, sat
from tea.evaluate_data_structures import VarData, CombinedData, BivariateData, MultivariateData
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
    properties_for_vars: Dict["Property", List[int]]

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
        global __test_map__
        self.name = name
        self.test_vars = test_vars
    
        if test_properties is None:
            test_properties = []
        
        if properties_for_vars is None:
            properties_for_vars = {}

        self.test_properties = test_properties
        self.properties_for_vars = {}
        for key in properties_for_vars:
            indices = [self.test_vars.index(arg) for arg in properties_for_vars[key]]
            self.properties_for_vars[key] = indices
        
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
            import pdb; pdb.set_trace()
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

    def __init__(self, name, description, arity=1):
        self.name = name
        self.description = description
        self.arity = arity
        args = []
        for _ in range(self.arity):
            args.append(z3.BoolSort())
        args.append(z3.BoolSort())
        self.__z3__ = z3.Function(self.name, *args)
        self.__cache__ = {}

    def __str__(self):
        return f"property:{self.name}"

    def __repr__(self):
        return f"Property({self.name})"

    def __call__(self, *var_names):
        if len(var_names) != self.arity:
            raise Exception(f"{self.name} property has arity {self.arity} " \
                            f"found {len(var_names)} arguments")
        # cached = self.__cache__.get(tuple(var_names))
        # if cached:
        #     return cached
        
        ap = AppliedProperty(self, var_names)
        self.__cache__[tuple(var_names)] = ap
        return ap

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

one_x_variable = Property('one_x', "Exactly one explanatory variable")
all_x_variables_categorical = Property('all_x_cat', "All explanatory variables are categorical")
two_x_variable_categories = Property('two_x_var', "Exactly two categories in explanatory variable")
one_y_variable = Property('one_y_var', "Exactly one explained variable")

continuous = Property('continuous', "Continuous (not categorical) data")
normal = Property('normal', "Normal distribution")
paired = Property('paired', "Paired observations")
eq_variance = Property('equal_var', "Equal variance", 2)

two_categories_eq_variance = Property('two_cat_eq_var', "Two groups have equal variance", 2)

x = StatVar('x')
y = StatVar('y')
students_t = StatisticalTest('students_t', [x, y],
                            test_properties=
                                [one_x_variable, one_y_variable, paired],
                            properties_for_vars={ all_x_variables_categorical : [x],
                                  two_x_variable_categories: [x],
                                  continuous: [y],
                                  normal: [y],
                                  eq_variance: [x, y] # Not sure about this emjun
                                })
z = StatVar('z')
w = StatVar('w')
students_t.apply(z, w)

# Incremental solving or change encoding (from conjunction to DNF/...)
# If property is a negation of another property, would like to know (e.g., normal and not normal)
# -- could use function not()

def which_tests(props: list,  design):
    # Rule out statically
    # We don't need to pass information about StatisticalTest
    # properties because if one of the conditions doesn't hold, 
    # the entire StatisticalTest does not apply regardless of variable-specific properties

    # We first check if the StatisticalTest properties hold

    # If not, discard!

    # If so, build list
    # Then, generate query from set of Tests that are left. 
    # Assert the properties are true

    # Incremental nature: Property is true, but what if it wasn't?
    


    # query starts as empty
    s = z3.Solver()
    for prop in props:
        # for each prop p_N it becomes:
        # query /\ p_n = True 
        s.add(prop.__z3__ == z3.BoolVal(True))
    
    for test in all_tests():
        # query = query /\ test.query()
        s.add(test.query())
    
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
        import pdb; pdb.set_trace()
        # PEACH WRITE HERE


def which_props(tests: list):
    test_queries = []
    for test in tests:
        test_queries.append(test.__z3__ == z3.BoolVal(True))
        test_queries.append(test.query())
    query = z3.And(test_queries) # May want to change
    import pdb; pdb.set_trace()
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
            import pdb; pdb.set_trace()
            if prop and model[decl] == True:
                props.append(prop)
            else: 
                import pdb; pdb.set_trace()
        return props


ps = which_props([students_t])

# ts = which_tests(one_x_variable(students_t), 
#                  one_y_variable(students_t), 
#                  paired(students_t)],
#                             properties_for_vars={ all_x_variables_categorical : [x],
#                                   two_x_variable_categories: [x],
#                                   continuous: [y],
#                                   normal: [y],
#                                   eq_variance: [x, y] # Not sure about this emjun
#                                 })
import pdb; pdb.set_trace()

print(ps)
# If properties do not hold, need to go back to solver with partially concrete assertions
# Use user assumptions to drive verification
