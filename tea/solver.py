import attr
import z3
from z3 import is_true 
from tea.dataset import Dataset
from tea.evaluate_data_structures import VarData, CombinedData, BivariateData, MultivariateData
from tea.evaluate_helper_methods import get_data, compute_normal_distribution, compute_eq_variance
from tea.global_vals import *
from typing import Dict, List

# Prog -> List[StatisticalTest] -> Query
alpha = 0.01 # Default

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

# def subset_props(scope): 
#     """A helper for accessing subset of properties based on their scope (Test or variable, for now)"""
#     props = all_props()
#     selected_props = []
#     for p in props: 
#         if p.scope == scope:
#             selected_props.append(p)

#     return selected_props

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
            # Alternative: Assign test-level properties to all the variables rather than
            # the test name
            # self._properties.append(prop(StatVar(self.name)))
            variables = [v for v in self.test_vars]
            # import pdb; pdb.set_trace()
            self._properties.append(prop(*variables))

        for prop in self.properties_for_vars:
            list_of_variable_indices = self.properties_for_vars[prop]
            for variable_indices in list_of_variable_indices:
                variable_indices = [self.test_vars[i] for i in variable_indices]
                # import pdb; pdb.set_trace()
                self._properties.append(prop(*variable_indices))
    
    def properties(self):
        return self.test_properties + list(self.properties_for_vars)

    def query(self):  # May want to change this....
        global __property_to_function__

        self._populate_properties()  # Apply to specific instance of variables
        # if self.__query__ is None:
        conj = []
        for p in self._properties:  # combines Test and Var-specific properties
            # p.__z3__ = uninterpreted function
            # p.__var__ = instantiated z3 BoolVal
            # Add the uf, and interpret the uf as always ==ing the instantiated BoolVal
            # conj += [p.__z3__, p.__z3__ == p.__var__]
            conj += [p.__z3__]

            # Add property to property to function map
            __property_to_function__[p.__z3__] = p.property.function

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

@attr.s(hash=False, init=False, repr=False, str=False)
class Property:
    name: str
    description: str
    arity: int

    def __init__(self, name, description, function=None, arity=1):
        global __property_map__, __ALL_PROPERTIES__

        self.name = name
        self.description = description
        self.function = function
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

    # Only used when the property must be changed depending on input data
    def _update(self, arity):
        self.arity = arity
        self.reset()

    def reset(self):
        args = []
        for _ in range(self.arity):
            args.append(z3.BoolSort())
        args.append(z3.BoolSort())
        self.__z3__ = z3.Function(self.name, *args)  # e.g. continuous(x)

@attr.s(hash=False, init=False, repr=False, str=False)
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

# Functions to verify properties
def is_bivariate(dataset: Dataset, combined_data: CombinedData, alpha):
    return len(combined_data.vars) == 2
    # could also do...
    # return isinstance(combined_data, BivariateData)

def is_multivariate(datset: Dataset, combined_data: CombinedData, alpha):
    return len(combined_data.vars) > 2
    # could also do...
    # return isinstance(combined_data, MultivariateData)

def has_one_x(dataset: Dataset, combined_data: CombinedData, alpha): 
    xs = combined_data.get_explanatory_variables()

    return len(xs) == 1

def has_one_y(dataset: Dataset, combined_data: CombinedData, alpha): 
    ys = combined_data.get_explained_variables()

    return len(ys) == 1

def has_paired_observations(dataset: Dataset, combined_data: CombinedData, alpha):
    global paired

    return combined_data.properties[paired]

def has_independent_observations(dataset: Dataset, combined_data: CombinedData, alpha):
    global paired

    return not combined_data.properties[paired]

def has_equal_variance(dataset: Dataset, combined_data: CombinedData, alpha):
    xs = None
    ys = None
    cat_xs = []
    cont_ys = []
    grouped_data = []
    
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()

    for x in xs: 
        if x.is_categorical(): 
            cat_xs.append(x)
    
    for y in ys: 
        if y.is_continuous(): 
            cont_ys.append(y)
    
    if cat_xs and cont_ys: 
        for y in ys:
            for x in xs: 
                cat = [k for k,v in x.metadata[categories].items()]
                for c in cat: 
                    data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
                    grouped_data.append(data)
                if isinstance(combined_data, BivariateData):
                    # Equal variance
                    eq_var = compute_eq_variance(grouped_data)
                # elif isinstance(combined_data, MultivariateData):
                #     combined_data.properties[eq_variance + '::' + x.metadata[name] + ':' + y.metadata[name]] = compute_eq_variance(grouped_data)
                else: 
                    raise ValueError(f"combined_data_data object is neither BivariateData nor MultivariateData: {type(combined_data)}")

    return (eq_var[1] < alpha)

def has_groups_normal_distribution(dataset, combined_data, alpha):
    xs = None
    ys = None
    cat_xs = []
    cont_ys = []
    grouped_data = []
    
    xs = combined_data.get_explanatory_variables()
    ys = combined_data.get_explained_variables()

    for x in xs: 
        if x.is_categorical(): 
            cat_xs.append(x)
    
    for y in ys: 
        if y.is_continuous(): 
            cont_ys.append(y)
    
    if cat_xs and cont_ys: 
        for y in ys:
            for x in xs: 
                cat = [k for k,v in x.metadata[categories].items()]
                for c in cat: 
                    data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
                    grouped_data.append(data)

                for group in grouped_data:
                    group_normal_test_results = compute_normal_distribution(group)
                    if (group_normal_test_results[1] <= alpha):
                        return False

    return True

def is_categorical_var(dataset, var_data, alpha):
    assert(len(var_data) == 1)
    assert(isinstance(var_data[0], VarData))

    return var_data[0].is_categorical()

def has_two_categories(dataset, var_data, alpha): 
    assert(len(var_data) == 1)
    assert(isinstance(var_data[0], VarData))

    # First check that the variable is categorical
    assert(is_categorical_var(dataset, var_data, alpha))
    return len(var_data[0].metadata[categories].keys()) == 2

def is_continuous_var(dataset, var_data, alpha):
    assert(len(var_data) == 1)
    assert(isinstance(var_data[0], VarData))

    return var_data[0].is_continuous()

def is_continuous_or_ordinal_var(dataset, var_data, alpha):
    assert(len(var_data) == 1)
    assert(isinstance(var_data[0], VarData))

    return is_continuous_var(dataset, var_data, alpha) or var_data[0].is_ordinal()

def has_normal_distribution(dataset, var_data, alpha):
    assert(len(var_data) == 1)
    assert(isinstance(var_data[0], VarData))

    # Must be continuous to be normally distributed
    assert(is_continuous_var(dataset, var_data, alpha))
    # Get data from datasest using var_data's query 
    data = get_data(dataset, var_data[0])
    norm_test_results = compute_normal_distribution(data)

    return (norm_test_results[1] > alpha)

# Test properties
bivariate = Property('is_bivariate', "Exactly two variables involved in analysis", is_bivariate)
multivariate = Property('is_multivariate', "More than two variables involved in analysis", is_multivariate) # May not need this!
one_x_variable = Property('has_one_x', "Exactly one explanatory variable", has_one_x)
one_y_variable = Property('has_one_y', "Exactly one explained variable", has_one_y)
paired_obs = Property('has_paired_observations', "Paired observations", has_paired_observations)
independent_obs = Property('has_independent_observations', "Independent (not paired) observations", has_independent_observations)
# not_paired = Property('not_paired', "Paired observations") 

test_props = [bivariate, one_x_variable, one_y_variable, paired_obs, independent_obs]

# Variable properties
categorical = Property('is_categorical', "Variable is categorical", is_categorical_var)
two_categories = Property('has_two_categories', "Variable has two categories", has_two_categories)
# all_x_variables_categorical = Property('has_all_x_categorical', "All explanatory variables are categorical", 'variable')
# two_x_variable_categories = Property('has_two_categories_x_var', "Exactly two categories in explanatory variable", 'variable')
continuous = Property('is_continuous', "Continuous (not categorical) data", is_continuous_var)
# We could create a disjunction of continuous \/ ordinal instead
continuous_or_ordinal = Property('is_continuous_or_ordinal', "Continuous OR ORDINAL (not nominal) data", is_continuous_or_ordinal_var)
groups_normal = Property('is_groups_normal', "Groups are normally distributed", has_groups_normal_distribution, arity=2)
normal = Property('is_normal', "Normal distribution", has_normal_distribution)
eq_variance = Property('has_equal_variance', "Equal variance", has_equal_variance, arity=2)


# two_categories_eq_variance = Property('two_cat_eq_var', "Two groups have equal variance", 'variable', 2)

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

def construct_test_axioms(solver):
    solver.add(paired_obs.__z3__ != independent_obs.__z3__)
    

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

        # If a variable is continuous or ordinal, it must be continuous.
        _axioms.append(z3.Implies(continuous_or_ordinal(var).__z3__, continuous(var).__z3__))

        # If a variable has two categories, then it must be categorical.
        # _axioms.append(z3.Implies(two_x_variable_categories(var).__z3__, categorical(var).__z3__))

    return _axioms


# Multivariate tests that accept variable 

spearmanr_corr = None
kendalltau_corr = None
pointbiserial_corr = None

# The generic StatisticalTests have specific predefined arity.
# Some multivariate statistical tests, however, have various arities. 
# Therefore, support the construction of muliple generic StatisticalTests. 
def construct_mutlivariate_tests(combined_data): 
    construct_pearson_corr(combined_data)    
    
def construct_pearson_corr(combined_data): 
    global pearson_corr

    num_vars = len(combined_data.vars)

    generic_vars = []
    for i in range(num_vars): 
        name = 'x' + str(i)
        generic_vars.append(StatVar(name))
    assert(num_vars == len(generic_vars))

    test_props = []
    if num_vars == 2: 
        test_props.append(bivariate)
    else: 
        test_props.append(multivariate)
    
    list_generic_vars = [[v] for v in generic_vars]
    pearson_corr = StatisticalTest('pearson_corr', generic_vars, 
                                    test_properties=
                                    test_props,
                                    properties_for_vars={
                                        continuous: list_generic_vars,
                                        normal: list_generic_vars
                                    })
    
def construct_kendalltau_corr(combined_data): 
    global kendalltau_corr

    num_vars = len(combined_data.vars)

    generic_vars = []
    for i in range(num_vars): 
        name = 'x' + str(i)
        generic_vars.append(StatVar(name))
    assert(num_vars == len(generic_vars))

    test_props = []
    if num_vars == 2: 
        test_props.append(bivariate)
    else: 
        test_props.append(multivariate)
    
    list_generic_vars = [[v] for v in generic_vars]
    kendalltau_corr = StatisticalTest('kendalltau_corr', generic_vars, 
                                    test_properties=
                                    test_props,
                                    properties_for_vars={
                                        continuous: list_generic_vars,
                                        normal: list_generic_vars
                                    })

    # Really naive way: 
    # Pearson correlation 

    # Tau correlation 

    #....

    # enumerate all tests that have variable arities. 
    # Pro: Reuse StatVars
    # Con: Hard to extend??
    # for test in multivariate_tests: 

    


x = StatVar('x')
y = StatVar('y')


# pearson_corr = StatisticalTest('pearson_corr', [x,y],
#                                 test_properties=
#                                 [bivariate],
#                                 properties_for_vars={
#                                     continuous: [[x], [y]]
#                                 })

students_t = StatisticalTest('students_t', [x, y],
                            test_properties=
                                [bivariate, one_x_variable, one_y_variable, independent_obs],
                            properties_for_vars={
                                  categorical : [[x]],
                                  two_categories: [[x]],
                                  continuous: [[y]],
                                  groups_normal: [[x, y]],
                                  eq_variance: [[x, y]] 
                                })

paired_students_t = StatisticalTest('paired_students_t', [x, y],
                            test_properties=
                                [bivariate, one_x_variable, one_y_variable, paired_obs],
                            properties_for_vars={
                                  categorical : [[x]],
                                  two_categories: [[x]],
                                  continuous: [[y]],
                                  groups_normal: [[x, y]],
                                  eq_variance: [[x, y]]
                                })

welchs_t = StatisticalTest('welchs_t', [x, y],
                            test_properties=
                                [bivariate, one_x_variable, one_y_variable, independent_obs],
                            properties_for_vars={
                                  categorical : [[x]],
                                  two_categories: [[x]],
                                  continuous: [[y]],
                                  groups_normal: [[x, y]]
                                #   groups_normal: [[y]], # TODO: Check that each group is normally distributed
                                })

mannwhitney_u = StatisticalTest('mannwhitney_u', [x, y],
                            test_properties=
                                [one_x_variable, one_y_variable, independent_obs],
                            properties_for_vars={
                                  categorical : [[x]],
                                  two_categories: [[x]],
                                  continuous_or_ordinal: [[y]],
                                # conflicting sources, but remove for now
                                #   eq_variance: [x, y] # Is this an assumption of mann whitney??
                                })                                

"""

# Specify variable properties as list of lists so that the same property can
# apply to multiple variables individually. If "categorical" is specified twice,
# only the second variable is kept because it overwrites the first entry in the
# dictionary.
chi_square_test = StatisticalTest('chi_square', [x, y],
                                   test_properties=[one_x_variable, one_y_variable],
                                   properties_for_vars={
                                       categorical: [[x], [y]]
                                   })
"""

# Verify the property against data
def verify_prop(dataset: Dataset, combined_data: CombinedData, prop:AppliedProperty):
    global alpha

    if (len(prop.test_vars) == len(combined_data.vars)):
        kwargs = {'dataset': dataset, 'combined_data': combined_data, 'alpha': alpha}
        prop_val = __property_to_function__[prop.__z3__](**kwargs)    
    else: 
        assert (len(prop.test_vars) < len(combined_data.vars))
        var_data = []
        for test_var in prop.test_vars:
            for var in combined_data.vars:
                if var.metadata[name] == test_var.name:
                    var_data.append(var)
        kwargs = {'dataset': dataset, 'var_data': var_data, 'alpha': alpha}
        prop_val = __property_to_function__[prop.__z3__](**kwargs)
    
    return prop_val

# Assumes properties to hold
def assume_properties(assumptions: Dict[str,str], solver): 
    global assumptions_to_properties, alpha

    # Go through all assumptions
    for a in assumptions: 
        if a in alpha_keywords:
            alpha = float(assumptions[a])
        # Apply corresponding properties to all variables for which the property is assumed
        for prop in all_props(): 
            if a in assumptions_to_properties and prop.name == assumptions_to_properties[a]: 
                for var in assumptions[a]: 
                    ap = prop(StatVar(var))
                    solver.add(ap.__z3__ == z3.BoolVal(True))

# Problem statement: Given a set of properties, tell me which tests are valid to run
# This is a concrete (rather than symbolic) problem 
# @param combined_data CombinedData object
# @returns list of Property objects that combined_data exhibits
def synthesize_tests(dataset: Dataset, assumptions: Dict[str,str], combined_data: CombinedData):
    import pdb; pdb.set_trace()
    global name

    # Reorder variables so that y var is at the end
    combined_data._update_vars() 
    # Assume properties are True based on user assumptions
    solver = z3.Solver()
    # s = Tactic('qflia').solver()
    assume_properties(assumptions, solver)
    # Update the arity of test-level properties
    for prop in test_props: 
        prop._update(len(combined_data.vars))

    # Apply all tests to the variables we are considering now in combined_data
    # TODO: Need to update the properties so that their z3 variable gets updated, not just Property arity. 
    # Probably add a function to take care arity and z3??
    for test in all_tests(): 
        variables = combined_data.vars
        stat_vars = []
        for var in variables: 
            stat_vars.append(StatVar(var.metadata[name]))
        
        test.apply(*stat_vars)
    """
    # Maybe I don't need axioms because they are implicit in the verification step?
    import pdb; pdb.set_trace()
    construct_test_axioms(s)
    # The axioms need to be for particular instance of property variables (not generic variables)
    # Maybe we could add the generic and then prop()/call to make applied?? -- need correct z3 refs
    # What does Maureen do for synthesize_props??
    import pdb; pdb.set_trace()
    """
    solver.push() # Create backtracking point
    model = None # Store model

    # For each test, add it to the solver as a constraint. 
    # Add the tests and their properties
    for test in all_tests():
        solver.add(test.__z3__ == z3.And(*test.query()))
        solver.add(test.__z3__ == z3.BoolVal(True))

        # Check the model 
        result = solver.check()
        if result == z3.unsat:
            print("no more solutions")
            print(solver.num_scopes())
            solver.pop() 
            # model = solver.model() # may need to do a check before call model
        elif result == z3.unknown:
            print("failed to solve")
            try:
                print(solver.model())
            except z3.Z3Exception:
                return
        else:
            model = solver.model()
            test_invalid = False
            # Does the test apply?
            # Would this ever be false??
            if model and is_true(model.evaluate(test.__z3__)):
                # Verify the properties for that test
                for prop in test._properties:
                    # Does this property need to hold for the test to be valid?
                    # If so, verify that the property does hold
                    if model and is_true(model.evaluate(prop.__z3__)):
                        val = verify_prop(dataset, combined_data, prop)
                        if not val and not test_invalid: # The property does not check
                            solver.pop() # remove the last test
                            test_invalid = True
                            model = None
                        solver.add(prop.__z3__ == z3.BoolVal(val))
        solver.push() # Push latest state as backtracking point

    # import pdb; pdb.set_trace()
    tests_to_conduct = []
    # Could add all the test props first 
    # Then add all the tests 
    for test in all_tests():
        if model and is_true(model.evaluate(test.__z3__)):
            tests_to_conduct.append(test.name)
        elif not model: # No test applies
            pass

    return tests_to_conduct

def which_props(tests_names: list, var_names: List[str]):
    stat_vars: List[StatVar] = []
    for var_name in var_names:
        stat_vars.append(StatVar(var_name))

    axioms = construct_axioms(stat_vars)

    tests: List[StatisticalTest] = []
    for test_name in tests_names:
        for test in all_tests():
            if test.name == test_name:
                test.apply(*stat_vars)
                test._populate_properties() 
                tests.append(test)

    test_queries = []
    important_soft_constraints = []
    for test in tests:
        # The Bool representing whether the test can be run with the given property
        # values is a hard constraint because we want to satisfy all tests, but may
        # not be able to.
        important_soft_constraints.append(test.__z3__)

        # The relationship of the properties of variables required to run a specific
        # test is an axiom and cannot be violated.
        axioms.append(test.__z3__ == z3.And(*test.query()))

        # test_queries contains the individual property constraints (e.g. continuous(x)).
        # These will all be soft constraints with low weight because they may need to be
        # violated.
        test_queries += test.query()

    s = z3.Optimize()

    # Set weight of tests to large number so they are satisfied over properties.
    # print("\nImportant soft constraints:")
    for constraint in important_soft_constraints:
        # print(constraint)
        s.add_soft(constraint, 1000)

    # Prefer to violate properties by giving them low weight.
    # print("\nSoft constraints:")
    for soft_constraint in test_queries:
        # print(soft_constraint)
        s.add_soft(soft_constraint, 1)

    # Axioms cannot be violated.
    # print("\nHard constraints:")
    for axiom in axioms:
        # print(axiom)
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
                property_identifier = ""# test_property._name
                for test_var in test_property.test_vars:
                    property_identifier += "variable %s : " % test_var.name
                property_identifier += test_property._name
                property_result = bool(model.evaluate(test_property.__z3__))
                _tests_and_properties[test_name][property_identifier] = property_result
                if not property_result:
                    _test_to_broken_properties[test_name].append(property_identifier)

        return _tests_and_properties, _test_to_broken_properties


# test_to_properties, test_to_broken_properties = which_props([mannwhitney_u, students_t])

# # print(ps)
# import pprint
# pp = pprint.PrettyPrinter()
# print("\nProperties for student's t test and Mann Whitney u test are complementary.")
# print("\nProperties:")
# pp.pprint(test_to_properties)
# print("\nProperties that could not be satisfied:")
# pp.pprint(test_to_broken_properties)


# test_to_properties, test_to_broken_properties = which_props([mannwhitney_u, chi_square_test])

# # print(ps)
# import pprint
# print("\nProperties for Mann Whitney u test and the chi square test conflict.")
# pp = pprint.PrettyPrinter()
# print("\nFound properties:")
# pp.pprint(test_to_properties)
# print("\nProperties that could not be satisfied:")
# pp.pprint(test_to_broken_properties)
# # If properties do not hold, need to go back to solver with partially concrete assertions
# # Use user assumptions to drive verification
