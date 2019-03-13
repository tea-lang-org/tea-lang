import attr
# import z3
# from .global_vals import *
# from enum import Flag, auto
import z3
# from z3 import BoolVal, Bool, Optimize, And, sat
# from tea.evaluate_data_structures import VarData, CombinedData, BivariateData, MultivariateData
# from tea.global_vals import *
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

        # TODO: properties_for_vars will have to be able to map a property to multiple sets of vars.
        self.properties_for_vars = {}
        for key in properties_for_vars:
            for args in properties_for_vars[key]:
                indices = [self.test_vars.index(arg) for arg in args]
                # TODO: How does this work if the property is specified multiple times,
                # e.g. continuous(x) and continuous(y)
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
            list_of_vs = self.properties_for_vars[prop]
            for vs in list_of_vs:
                vs = [self.test_vars[i] for i in vs]
                # import pdb; pdb.set_trace()
                self._properties.append(prop(*vs))

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

        # query = {
        #     'hard_constraints': z3.And(*conj),
        #     'soft_constraints': self.__z3__
        # }
        # conj = conj + [self.__z3__]  # Why is this needed if we assert self.z3==True below?
        # query = z3.And(*conj)
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

    def __init__(self, name, description, arity=1):
        self.name = name
        self.description = description
        self.arity = arity
        args = []
        for _ in range(self.arity):
            args.append(z3.BoolSort())
        args.append(z3.BoolSort())
        self.__z3__ = z3.Function(self.name, *args)  # e.g. continuous(x)
        self.__cache__ = {}

    def __str__(self):
        return f"property:{self.name}"

    def __repr__(self):
        return f"Property({self.name})"

    def __call__(self, *var_names):
        if len(var_names) != self.arity:
            raise Exception(f"{self.name} property has arity {self.arity} "\
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
        self.property = prop  # e.g. continuous
        self.test_vars = test_vars  # (StatVar(name='x'),)
        self._name = ""
        z3_args = []
        for tv in test_vars:
            # Allows for unique identification of prop -> var, but not looking up from model because that refs prop name
            # self._name += tv.name + ":"
            # self._name + tv.name
            z3_args.append(tv.__z3__)
        self._name = self.property.name  # continuous
        # Why is property fn a bool? Does this allow continuous(x) and not continuous(y)?
        # self.__var__ = z3.Bool(self._name)  # e.g. continuous
        self.__z3__ = prop.__z3__(*z3_args)  # e.g. continuous(x)

        # _name needs to be unique to avoid overwriting same property for different variables.
        if self._name not in __property_var_map__.keys():
            __property_var_map__[self._name] = []

        __property_var_map__[self._name].append(test_vars)

    def __str__(self):
        return f"property_for_var:{self._name}"

    def __repr__(self):
        return f"AppliedProperty({self._name})"

    @staticmethod
    def get_by_z3_var(name):
        global __property_var_map__
        return __property_var_map__.get(name)


one_x_variable = Property('one_x', "Exactly one explanatory variable")  # test property
all_x_variables_categorical = Property('all_x_cat', "All explanatory variables are categorical")
two_x_variable_categories = Property('two_x_var', "Exactly two categories in explanatory variable")
one_y_variable = Property('one_y_var', "Exactly one explained variable")  # test property

categorical = Property('categorical', "Categorical (not continuous) data")
continuous = Property('continuous', "Continuous (not categorical) data")
normal = Property('normal', "Normal distribution")
paired = Property('paired', "Paired observations")  # test property
eq_variance = Property('equal_var', "Equal variance", 2)

two_categories_eq_variance = Property('two_cat_eq_var', "Two groups have equal variance", 2)


def construct_axioms(variables):  # List[StatVar]
    _axioms = []
    for var in variables:
        # A variable must be continuous or categorical, but not both.
        _axioms.append(z3.And(z3.Or(continuous(var).__z3__, categorical(var).__z3__),\
                             z3.Not(z3.And(continuous(var).__z3__, categorical(var).__z3__))))

        # If a variable is an explanatory variable and all explanatory variables are categorical,
        # then the variable must be categorical.
        # It isn't clear how to reason about whether a variable is an explanatory or explained variable.
        _axioms.append(z3.Implies(all_x_variables_categorical(var).__z3__, categorical(var).__z3__))

        # Not sure how to reason about test properties like one_x_variable and one_y_variable.
        # _axioms.append(z3.Not(z3.And(one_x_variable(var).__z3__, one_y_variable(var).__z3__)))

        # If a variable is normal, then it cannot be categorical.
        _axioms.append(z3.Implies(normal(var).__z3__, z3.Not(categorical(var).__z3__)))

        # If a variable has two categories, then it must be categorical.
        _axioms.append(z3.Implies(two_x_variable_categories(var).__z3__, categorical(var).__z3__))

    return _axioms


x = StatVar('x')
y = StatVar('y')
students_t = StatisticalTest('students_t', [x, y],
                             test_properties=
                             [one_x_variable, one_y_variable, paired],
                             properties_for_vars={all_x_variables_categorical: [[x]],
                                                  two_x_variable_categories: [[x]],
                                                  continuous: [[y]],
                                                  normal: [[y]],
                                                  eq_variance: [[x, y]]  # Not sure about this emjun
                                                  })

u_test = StatisticalTest('u_test', [x, y],
                         test_properties=
                         [one_x_variable, one_y_variable],
                         properties_for_vars={
                             all_x_variables_categorical: [[x]],
                             two_x_variable_categories: [[x]],
                             continuous: [[y]],
                         })

# Output has all_x_cat == False, but should be true because every variable is categorical,
# and one of them is the explanatory variable.
# How to specify this? Because now second categorical specification overwrites the first.
conflicting_test = StatisticalTest('conflict', [x, y],
                                   test_properties=[one_x_variable, one_y_variable],
                                   properties_for_vars={
                                       categorical: [[x], [y]]
                                   })

z = StatVar('z')
w = StatVar('w')
# students_t.apply(z, w)
u_test.apply(z, w)
conflicting_test.apply(z, w)


# variables = [z, w]
axioms = construct_axioms([z, w])

# It seems like there should be a way to wrap all_variables_categorical() using categorical()
# so that we can just check continuous(y) and categorical(y).
# all_variables_categorical(z, w) ==> categorical(z) ^ categorical(w)
# conflict_clauses = z3.Not(z3.And(continuous(w).__z3__, all_variables_categorical(z, w).__z3__))

# p = StatVar('p')
# q = StatVar('q')
# axiom1 = z3.ForAll([p.__z3__], z3.Not(z3.And(continuous(p).__z3__, categorical(p).__z3__)), weight=1000)
# axiom2 = z3.ForAll([p.__z3__, q.__z3__],\
#                    z3.Implies(all_variables_categorical(p, q).__z3__,\
#                               z3.And(categorical(p).__z3__, categorical(q).__z3__)), weight=1000)
# axioms = [axiom1, axiom2]

# print(axioms)

# Incremental solving or change encoding (from conjunction to DNF/...)
# If property is a negation of another property, would like to know (e.g., normal and not normal)
# -- could use function not()

def which_tests(props: list, design):
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
        print("else")
        # import pdb; pdb.set_trace()
        # PEACH WRITE HERE


def which_props(tests: list):
    test_queries = []
    hard_constraints = []
    for test in tests:
        # TODO: This isn't meaningful without an iff with related constraints.
        hard_constraints.append(test.__z3__)
        axioms.append(test.__z3__ == z3.And(*test.query()))
        test_queries += test.query()
    # query = z3.And(test_queries) # May want to change
    # import pdb; pdb.set_trace()
    # s = z3.Solver()
    # s.set(unsat_core=True)
    #
    # s.add(query)
    s = z3.Optimize()

    # Set weight of tests to large number so they are satisfied over properties.
    print("\nHard constraints:")
    for constraint in hard_constraints:
        print(constraint)
        s.add_soft(constraint, 1000)

    # Test properties can be violated.
    print("\nSoft constraints:")
    for soft_constraint in test_queries:
        print(soft_constraint)
        s.add_soft(soft_constraint, 1)

    # Axioms cannot be violated.
    print("\nAxioms:")
    for axiom in axioms:
        print(axiom)
        s.add(axiom)

    # s.assert_and_track(conflict_clauses, "conflicts")
    # for idx, axiom in enumerate(axioms):
    #     s.assert_and_track(axiom, "a%d"%idx)
    result = s.check()
    # WARNING: optimization with quantified constraints is not supported
    if result == z3.unsat:
        print("no solution")
        # print("unsat core: %s" % s.unsat_core())
    elif result == z3.unknown:
        print("failed to solve")
        try:
            print(s.model())
        except z3.Z3Exception:
            return
    else:
        # model.evaluate(categorical.__z3__(w.__z3__))
        model = s.model()
        test_to_properties = {}
        test_to_broken_properties = {}
        for test in tests:
            test_name = test.name
            test_to_properties[test_name] = {}
            test_to_broken_properties[test_name] = []
            for property in test._properties:
                print("property: %s" % property)
                property_identifier = property._name
                for test_var in property.test_vars:
                    property_identifier += "_%s" % test_var.name
                property_result = bool(model.evaluate(property.__z3__))
                test_to_properties[test_name][property_identifier] = property_result
                if not property_result:
                    test_to_broken_properties[test_name].append(property_identifier)

        return test_to_properties, test_to_broken_properties

        # props = []
        # for decl in model.decls():
        #     # TODO: Failed to evaluate anything on z. Only w.
        #     # maybe because applied property name is same for both vars?
        #
        #     # TODO: Need to make sure to only print properties that are specified by the tests.
        #     associated_variables = AppliedProperty.get_by_z3_var(decl.name())
        #
        #     # import pdb; pdb.set_trace()
        #     if associated_variables:
        #         deduplicated_variables = set(associated_variables)
        #         for stat_vars in deduplicated_variables:
        #             print("\nstat_vars: %s" % stat_vars)
        #             assert len(stat_vars) == decl.arity(),\
        #                 "Wrong number of variables apply property to. " \
        #                 "Expected %d, got %d" % (decl.arity(), len(stat_vars))
        #
        #             print("\nEvaluate %s:\n" % decl.name())
        #             print(model.evaluate(decl(*[svar.__z3__ for svar in stat_vars])))
        #             print("\n")

            # if prop and model[decl] == True:
            #     props.append(prop)
            # else:
            #     print("else")
                # import pdb; pdb.set_trace()
        # return props


test_to_properties, test_to_broken_properties = which_props([u_test, conflicting_test])

# ts = which_tests(one_x_variable(students_t), 
#                  one_y_variable(students_t), 
#                  paired(students_t)],
#                             properties_for_vars={ all_x_variables_categorical : [x],
#                                   two_x_variable_categories: [x],
#                                   continuous: [y],
#                                   normal: [y],
#                                   eq_variance: [x, y] # Not sure about this emjun
#                                 })
# import pdb; pdb.set_trace()

print("\nFound properties:")
print(test_to_properties)
print("\nProperties that could not be satisfied:")
print(test_to_broken_properties)
# If properties do not hold, need to go back to solver with partially concrete assertions
# Use user assumptions to drive verification
