from tea.global_vals import *
from tea.helpers.constants.default_values import DEFAULT_ALPHA_PARAMETER
from tea.runtimeDataStructures.dataset import Dataset
from tea.runtimeDataStructures.varData import VarData
from tea.runtimeDataStructures.combinedData import CombinedData
from tea.runtimeDataStructures.bivariateData import BivariateData
from tea.helpers.evaluateHelperMethods import get_data, compute_normal_distribution, compute_eq_variance
# from tea.z3_solver.solver
from tea.logging.tea_logger import TeaLogger

import attr
import z3
from typing import Dict, List


# Prog -> List[StatisticalTest] -> Query
alpha = DEFAULT_ALPHA_PARAMETER
MODE = 'strict' # Default

# Contains a map from z3 variables representing tests
# back to the test objects allowing us to map back
# from a model back to the tests.
__test_map__ = {}

#  A list of all tests in the system which we can use
# to iterate over all tests.
__ALL_TESTS__ = None

def all_tests():
    """A helper for accessing the global set of tests"""
    global __ALL_TESTS__
    return __ALL_TESTS__

def reset_all_tests(): 
    global __test_map__, __ALL_TESTS__,__property_to_function__
    global pearson_corr, kendalltau_corr, pointbiserial_corr_a, pointbiserial_corr_b
    global students_t, paired_students_t, welchs_t, mannwhitney_u
    global chi_square, fishers_exact
    global f_test, rm_one_way_anova, kruskall_wallis, friedman, factorial_ANOVA

    pearson_corr = None
    kendalltau_corr = None
    spearman_corr = None
    pointbiserial_corr_a = None
    pointbiserial_corr_b = None
    students_t = None
    paired_students_t = None
    welchs_t = None 
    mannwhitney_u = None
    wilcoxon_signed_rank = None
    chi_square = None
    fishers_exact = None
    f_test = None    
    rm_one_way_anova = None
    kruskall_wallis = None
    friedman = None
    factorial_ANOVA = None
    
    __test_map__ = {}
    __ALL_TESTS__ = None
    __property_to_function__ = {}
    __property_var_map__ = {}

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


def set_mode(mode): 
    global MODE
    MODE = mode


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
            for prop_args in properties_for_vars[key]:
                indices = []
                # if self.name == 'pointbiserial_corr_a': 
                #     import pdb; pdb.set_trace()
                # if self.name == 'factorial_ANOVA': 
                #     import pdb; pdb.set_trace()
                indices = [self.test_vars.index(arg) for arg in prop_args]
                if key not in self.properties_for_vars.keys():
                    self.properties_for_vars[key] = []
                self.properties_for_vars[key].append(indices)

        # Create variable.
        self.__z3__ = z3.Bool(self.name)

        # Populate global table.
        __test_map__[self.__z3__] = self
        if not __ALL_TESTS__: 
            __ALL_TESTS__ = []
        __ALL_TESTS__.append(self)

    # Question: does this mean you can't consider two tests of the same type on different variables at once?
    def apply(self, *test_vars):
        # if len(test_vars) != len(self.test_vars): 
        #     import pdb; pdb.set_trace()
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
            self._properties.append(prop(*variables))

        for prop in self.properties_for_vars:
            list_of_variable_indices = self.properties_for_vars[prop]
            for variable_indices in list_of_variable_indices:
                variable_indices = [self.test_vars[i] for i in variable_indices]
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

    def __eq__(self, other):
        return self.arity == other.arity and self.name == other.name and self.function == other.function

    def __hash__(self):
        return hash((self.arity, self.name, self.function))

    def __call__(self, *var_names):
        # import pdb; pdb.set_trace()
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


class AppliedProperty:
    property: Property

    def __init__(self, prop, pvars):
        global __property_var_map__
        self.property = prop  # e.g. continuous
        self.vars = pvars  # (StatVar(name='x'),)
        # self._name = ""
        z3_args = []
        for tv in pvars:
            # Allows for unique identification of prop -> var, but not looking up from model because that refs prop name
            # self._name += tv.name + ":"
            # self._name + tv.name
            # import pdb; pdb.set_trace()
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
        __property_var_map__[self._name].append(self.vars)

        self.property_test_results = None

    def __str__(self):
        return f"property_for_var:{self._name}"

    def __repr__(self):
        return f"AppliedProperty({self._name})"
    
    def __eq__(self, other):
        return self.property == other.property and self.vars == other.vars

    @staticmethod
    def get_by_z3_var(name):
        global __property_var_map__
        return __property_var_map__.get(name)


# Functions to verify properties
def is_bivariate(dataset: Dataset, var_data: CombinedData, alpha):
    return len(var_data.vars) == 2
    # could also do...
    # return isinstance(var_data, BivariateData)


def is_multivariate(datset: Dataset, var_data: CombinedData, alpha):
    return len(var_data.vars) > 2
    # could also do...
    # return isinstance(var_data, MultivariateData)


def has_one_x(dataset: Dataset, var_data: CombinedData, alpha): 
    xs = var_data.get_explanatory_variables()

    return len(xs) == 1


def has_one_y(dataset: Dataset, var_data: CombinedData, alpha): 
    ys = var_data.get_explained_variables()

    return len(ys) == 1


def has_paired_observations(dataset: Dataset, var_data: CombinedData, alpha):
    global paired

    return var_data.properties[paired]


def has_independent_observations(dataset: Dataset, var_data: CombinedData, alpha):
    global paired

    return not var_data.properties[paired]


def greater_than_5_frequency(dataset: Dataset, var_data: CombinedData, alpha): 
    xs = var_data.get_explanatory_variables()
    ys = var_data.get_explained_variables()

    if len(xs) == 1: 
        if len(ys) == 1: 
            x = xs[0]
            y = ys[0]

            if x.is_categorical() and y.is_categorical(): 

                # Get the count for each category
                x_cat = [k for k , v in x.metadata[categories].items()]
                y_cat = [k for k , v in y.metadata[categories].items()]

                for xc in x_cat: 
                    for yc in y_cat: 
                        data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{xc}'", f"{y.metadata[name]} == '{yc}'"])                    

                        # Check that the count is at least five for each of the (x,y) group pairs
                        if len(data) < 5:
                            return False
                
                return True
            else: 
                return False
        else: 
            raise ValueError(f"Currently, chi square requires/only supports 1 explained variable, instead received: {len(ys)} -- {ys}")    
    else: 
        x0 = xs[0]
        x1 = xs[1]
        
        if x0.is_categorical() and x1.is_categorical():
            # Get the count for each category
            x0_cat = [k for k , v in x0.metadata[categories].items()]
            x1_cat = [k for k , v in x1.metadata[categories].items()]

            for x0c in x0_cat: 
                for x1c in x1_cat: 
                    data = dataset.select(x1.metadata[name], where=[f"{x.metadata[name]} == '{xc}'", f"{x1.metadata[name]} == '{x1c}'"])                    

                    # Check that the count is at least five for each of the (x,x1) group pairs
                    if len(data) < 5:
                        return False
            return True
        else: 
            return False



def has_equal_variance(dataset: Dataset, var_data: list, alpha):
    xs = []
    ys = []
    cat_xs = []
    cont_ys = []
    grouped_data = []


    if isinstance(var_data, CombinedData):
        xs = var_data.get_explanatory_variables()
        ys = var_data.get_explained_variables()

    else: 
        for var in var_data: 
            if var.role == iv_identifier or var.role == contributor_identifier:
                xs.append(var)
            if var.role == dv_identifier or var.role == outcome_identifier:
                ys.append(var)

    for x in xs: 
        if x.is_categorical(): 
            cat_xs.append(x)
    
    for y in ys: 
        if y.is_continuous(): 
            cont_ys.append(y)
    
    eq_var = (None, None)
    if cat_xs and cont_ys: 
        for y in ys:
            for x in xs: 
                cat = [k for k,v in x.metadata[categories].items()]
                for c in cat: 
                    data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
                    grouped_data.append(data)
                if isinstance(var_data, BivariateData):
                    # Equal variance
                    eq_var = compute_eq_variance(grouped_data)
                else: 
                    eq_var = compute_eq_variance(grouped_data)

    if eq_var[0] is None and eq_var[1] is None:
        # import pdb; pdb.set_trace()
        # raise Exception("did not compute variance, this is a bug")
        return False

    return eq_var[1] > alpha


def has_groups_normal_distribution(dataset, var_data, alpha):
    xs = []
    ys = []
    cat_xs = []
    cont_ys = []
    grouped_data = []
    result = None

    if isinstance(var_data, CombinedData):
        xs = var_data.get_explanatory_variables()
        ys = var_data.get_explained_variables()

    else: 
        for var in var_data: 
            if var.role == iv_identifier or var.role == contributor_identifier:
                xs.append(var)
            if var.role == dv_identifier or var.role == outcome_identifier:
                ys.append(var)

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
                    if isinstance(c, str):
                        data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == '{c}'"])
                    else: 
                        data = dataset.select(y.metadata[name], where=[f"{x.metadata[name]} == {c}"])
                    grouped_data.append(data)

                for group in grouped_data:
                    result = compute_normal_distribution(group)
                    if result[1] <= alpha:
                        return False, result

    return True, result


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


def has_two_or_more_categories(dataset, var_data, alpha): 
    assert(len(var_data) == 1)
    assert(isinstance(var_data[0], VarData))

    # First check that the variable is categorical
    assert(is_categorical_var(dataset, var_data, alpha))
    return len(var_data[0].metadata[categories].keys()) >= 2


def has_three_or_more_categories(dataset, var_data, alpha): 
    assert(len(var_data) == 1)
    assert(isinstance(var_data[0], VarData))

    # First check that the variable is categorical
    assert(is_categorical_var(dataset, var_data, alpha))
    return len(var_data[0].metadata[categories].keys()) >= 3


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

    return (norm_test_results[1] > alpha), norm_test_results


# Test properties
bivariate = Property('is_bivariate', "Exactly two variables involved in analysis", is_bivariate)
multivariate = Property('is_multivariate', "More than two variables involved in analysis", is_multivariate) # May not need this!
one_x_variable = Property('has_one_x', "Exactly one explanatory variable", has_one_x)
one_y_variable = Property('has_one_y', "Exactly one explained variable", has_one_y)
paired_obs = Property('has_paired_observations', "Paired observations", has_paired_observations)
independent_obs = Property('has_independent_observations', "Independent (not paired) observations", has_independent_observations)
greater_than_5_freq = Property('greater_than_5_freq', "Has a large sample size", greater_than_5_frequency, arity=2)

test_props = [bivariate, one_x_variable, one_y_variable, paired_obs, independent_obs]

# Variable properties
categorical = Property('is_categorical', "Variable is categorical", is_categorical_var)
two_categories = Property('has_two_categories', "Variable has two categories", has_two_categories)
two_or_more_categories = Property('has_two_or_more_categories', "Variable has two or more categories", has_two_or_more_categories)
three_or_more_categories = Property('has_three_or_more_categories', "Variable has three or more categories", has_three_or_more_categories)
# all_x_variables_categorical = Property('has_all_x_categorical', "All explanatory variables are categorical", 'variable')
# two_x_variable_categories = Property('has_two_categories_x_var', "Exactly two categories in explanatory variable", 'variable')
continuous = Property('is_continuous', "Continuous (not categorical) data", is_continuous_var)
# We could create a disjunction of continuous \/ ordinal instead
continuous_or_ordinal = Property('is_continuous_or_ordinal', "Continuous OR ORDINAL (not nominal) data", is_continuous_or_ordinal_var)
groups_normal = Property('is_groups_normal', "Groups are normally distributed", has_groups_normal_distribution, arity=2)
normal = Property('is_normal', "Normal distribution", has_normal_distribution)
eq_variance = Property('has_equal_variance', "Equal variance", has_equal_variance, arity=2)


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


bivariate_constructed = False
multivariate_constructed = False


# Constructs all the tests once
# TODO: Move to a separate file/location
def construct_all_tests(combined_data: CombinedData): 
    # global bivariate_constructed, multivariate_constructed

    # if not bivariate_constructed: 
    #     construct_bivariate_tests(combined_data)
    #     bivariate_constructed = True

    # if not multivariate_constructed: 
    #     construct_mutlivariate_tests(combined_data)
    #     multivariate_constructed = True

    construct_bivariate_tests(combined_data)
    construct_mutlivariate_tests(combined_data)


# The generic StatisticalTests have specific predefined arity.
# Some multivariate statistical tests, however, have various arities. 
# Therefore, support the construction of muliple generic StatisticalTests. 
def construct_mutlivariate_tests(combined_data):
    construct_factorial_ANOVA(combined_data)
    # pass


factorial_ANOVA = None


def construct_factorial_ANOVA(combined_data: CombinedData): 
    global factorial_ANOVA

    num_vars = len(combined_data.vars)

    x_vars = []
    y_vars = []
    all_vars = []
    for i in range(num_vars): 
        name = 'x' + str(i)
        # combined_data.vars[i].get_name()
        # import pdb; pdb.set_trace()
        if (i <= num_vars - 2): # All but the last var
            x = StatVar(name)
            x_vars.append(x)
            all_vars.append(x)
        else:
            assert(i == num_vars - 1)
            name = 'y' + str(i)
            y = StatVar(name)
            y_vars.append(y) # last var
            all_vars.append(y)
    assert(num_vars == len(x_vars) + len(y_vars))

    list_x_vars = [[v] for v in x_vars]
    # list_y_vars = [[v] for v in y_vars]
    # list_all_vars = list_x_vars + list_y_vars

    assert(len(y_vars) == 1)
    pairs_list = [[x, y_vars[0]] for x in x_vars]

    factorial_ANOVA = StatisticalTest('factorial_ANOVA', all_vars, # Variable number of factors
                                test_properties=
                                [one_y_variable],
                                # [one_y_variable, two_or_more_x_variables],
                                properties_for_vars={
                                continuous: [y_vars],
                                categorical: list_x_vars, # Variable number of factors
                                two_or_more_categories: list_x_vars,
                                groups_normal: pairs_list, # Variable number of factors
                                eq_variance: pairs_list # Variable number of factors
                                }) 


pearson_corr = None
kendalltau_corr = None
spearman_corr = None
pointbiserial_corr_a = None
pointbiserial_corr_b = None
students_t = None
paired_students_t = None
welchs_t = None 
mannwhitney_u = None
chi_square = None
fishers_exact = None 
f_test = None    
rm_one_way_anova = None
kruskall_wallis = None
friedman = None


def construct_bivariate_tests(combined_data: CombinedData): 
    global pearson_corr, kendalltau_corr, spearman_corr, pointbiserial_corr_a, pointbiserial_corr_b
    global students_t, paired_students_t, welchs_t, mannwhitney_u
    global chi_square, fishers_exact
    global f_test, kruskall_wallis, friedman, rm_one_way_anova

    # Bivariate analyses only make sense when there are two variables
    # in combined_data
    if len(combined_data.vars) == 2: 

        # CORRELATIONS
        x0 = StatVar('x0')
        x1 = StatVar('x1')

        pearson_corr = StatisticalTest('pearson_corr', [x0, x1],
                                        test_properties=
                                        [bivariate],
                                        properties_for_vars={
                                            continuous: [[x0], [x1]],
                                            normal: [[x0], [x1]]
                                        })

        kendalltau_corr = StatisticalTest('kendalltau_corr', [x0, x1],
                                        test_properties=
                                        [bivariate],
                                        properties_for_vars={
                                            continuous_or_ordinal: [[x0], [x1]]
                                        })

        spearman_corr = StatisticalTest('spearman_corr', [x0, x1],
                                        test_properties=
                                        [bivariate],
                                        properties_for_vars={
                                            continuous_or_ordinal: [[x0], [x1]]
                                        })

        # Need both? in case order of categortical and continuous differs?
        # TODO: Could just sort before apply test?
        pointbiserial_corr_a = StatisticalTest('pointbiserial_corr_a', [x0, x1],
                                        test_properties=
                                        [bivariate, independent_obs],
                                        properties_for_vars={
                                            continuous: [[x1]],
                                            # normal: [[x1]],
                                            groups_normal: [[x0, x1]],
                                            categorical: [[x0]],
                                            two_categories: [[x0]],
                                            eq_variance: [[x0, x1]]

                                        })

        pointbiserial_corr_b = StatisticalTest('pointbiserial_corr_b', [x0, x1],
                                        test_properties=
                                        [bivariate, independent_obs],
                                        properties_for_vars={
                                            continuous: [[x0]],
                                            # normal: [[x0]],
                                            groups_normal: [[x1, x0]],
                                            categorical: [[x1]],
                                            two_categories: [[x1]],
                                            eq_variance: [[x1, x0]]
                                        })                                

        # T-TESTS
        x = StatVar('x')
        y = StatVar('y')

        students_t = StatisticalTest('students_t', [x, y],
                                    test_properties=
                                        [bivariate, one_x_variable, one_y_variable, independent_obs],
                                    properties_for_vars={
                                        categorical : [[x]],
                                        two_categories: [[x]],
                                        continuous: [[y]],
                                        eq_variance: [[x, y]],
                                        groups_normal: [[x, y]]
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
        
        wilcoxon_signed_rank = StatisticalTest('wilcoxon_signed_rank', [x, y],
                                    test_properties=
                                        [bivariate, one_x_variable, one_y_variable, paired_obs],
                                    properties_for_vars={
                                        categorical : [[x]],
                                        two_categories: [[x]],
                                        continuous: [[y]],
                                        })

        # CONTINGENCY TABLES (Categorical data)
        chi_square = StatisticalTest('chi_square', [x, y],
                                        test_properties=
                                        [bivariate, independent_obs, greater_than_5_freq],
                                        properties_for_vars={
                                            categorical:  [[x], [y]],
                                            two_or_more_categories: [[x],[y]]
                                        })                       

        fishers_exact = StatisticalTest('fishers_exact', [x, y],
                                        test_properties=
                                        [bivariate, independent_obs],
                                        properties_for_vars={
                                            categorical:  [[x], [y]],
                                            two_categories: [[x],[y]]
                                        })

        # ANOVAs
        f_test = StatisticalTest('f_test', [x, y], # Variable number of factors
                                    test_properties=
                                    [independent_obs, one_x_variable, one_y_variable],
                                    properties_for_vars={
                                    continuous: [[y]],
                                    categorical: [[x]], # Variable number of factors
                                    two_or_more_categories: [[x]],
                                    groups_normal: [[x, y]], # Variable number of factors
                                    eq_variance: [[x, y]] # Variable number of factors
                                    }) 
        
        kruskall_wallis = StatisticalTest('kruskall_wallis', [x, y], # Variable number of factors
                                    test_properties=
                                    [independent_obs, one_x_variable, one_y_variable],
                                    properties_for_vars={
                                    continuous: [[y]],
                                    categorical: [[x]], # Variable number of factors
                                    two_or_more_categories: [[x]]
                                    })

        
        rm_one_way_anova = StatisticalTest('rm_one_way_anova', [x, y], # Variable number of factors
                                test_properties=
                                [paired_obs, one_x_variable, one_y_variable],
                                properties_for_vars={
                                continuous: [[y]],
                                categorical: [[x]], # Variable number of factors
                                two_or_more_categories: [[x]],
                                groups_normal: [[x, y]], # Variable number of factors
                                eq_variance: [[x, y]] # Variable number of factors
                                }) 

        friedman = StatisticalTest('friedman', [x,y], # Variable number of factors
                                test_properties=
                                [paired_obs, one_x_variable, one_y_variable],
                                properties_for_vars={
                                continuous: [[y]],
                                categorical: [[x]], # Variable number of factors
                                three_or_more_categories: [[x]],
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

    if len(prop.vars) == len(combined_data.vars):
        kwargs = {'dataset': dataset, 'var_data': combined_data, 'alpha': alpha}
        # import pdb; pdb.set_trace()
        if __property_to_function__ == {}:
            # import pdb; pdb.set_trace()
            prop_val = prop.property.function(**kwargs)
        else: 
            prop_val = __property_to_function__[prop.__z3__](**kwargs)   
    else: 
        assert (len(prop.vars) < len(combined_data.vars))
        var_data = []
        # For each of the variables for which we are checking the current prop
        for test_var in prop.vars:
            # For each variable in all variables in combined data
            for var in combined_data.vars:
                if var.metadata[name] == test_var.name:
                    var_data.append(var)
        kwargs = {'dataset': dataset, 'var_data': var_data, 'alpha': alpha}
        if __property_to_function__ == {}:
            prop_val = prop.property.function(**kwargs)
        else: 
            prop_val = __property_to_function__[prop.__z3__](**kwargs)

    ret_val = None
    if isinstance(prop_val, tuple):
        assert len(prop_val) == 2
        ret_val = prop_val[0]
        prop.property_test_results = prop_val[1]
    else:
        ret_val = prop_val
    
    return ret_val


# Assumes properties to hold
def assume_properties(stat_var_map, assumptions: Dict[str,str], solver, dataset, combined_data): 
    global assumptions_to_properties, alpha
    
    tea_logger = TeaLogger.get_logger()

    assumed_props = []

    # Go through all assumptions
    for a in assumptions: 
        if a in alpha_keywords:
            alpha = float(assumptions[a])
        elif a in assumptions_to_properties:
            # Apply corresponding properties to all variables for which the property is assumed
            for prop in all_props(): 
                if prop.name in assumptions_to_properties[a]: 
                    # Convert assumptions to use correct statistical variable names.
                    stat_vars = []
                    for var in assumptions[a]:
                        # This is really hacky -- should probably change the 
                        # incoming assumptions data structure before calling this method
                        if isinstance(var, str):
                            assert var in stat_var_map 
                            # stat_vars.append(stat_var_map[var]) 
                            ap = prop(stat_var_map[var]) 
                            assumed_props.append(ap)

                            # CHECK ASSUMPTIONS HERE
                            val = verify_prop(dataset, combined_data, ap)
                            if MODE == 'strict': 
                                tea_logger.log_debug(f"Running under STRICT mode.")
                                if val: 
                                    tea_logger.log_debug(f"User asserted property: {prop.name} is supported by statistical checking. Tea agrees with the user.")
                                else: 
                                    tea_logger.log_debug(f"User asserted property: {prop.name}, but is NOT supported by statistical checking. Tea will override user assertion.") 
                                solver.add(ap.__z3__ == z3.BoolVal(val))
                            elif MODE == 'relaxed': 
                                tea_logger.log_debug(f"Running under RELAXED mode.")
                                if val: 
                                    tea_logger.log_debug(f"User asserted property: {prop.name} is supported by statistical checking. Tea agrees with the user.")
                                else: 
                                    tea_logger.log_debug(f"User asserted property: {prop.name}, but is NOT supported by statistical checking. User assertion will be considered true.")
                                
                                solver.add(ap.__z3__ == z3.BoolVal(True))
                            else: 
                                raise ValueError(f"Invalid MODE: {MODE}")
                        else: 
                            assert isinstance(var, list)
                            stat_vars = [stat_var_map[v] for v in var]
                            ap = prop(*stat_vars)
                            assumed_props.append(ap)

                            # CHECK ASSUMPTIONS HERE
                            val = verify_prop(dataset, combined_data, ap)
                            if MODE == 'strict': 
                                tea_logger.log_debug(f"Running under STRICT mode.")
                                if val: 
                                    tea_logger.log_debug(f"User asserted property: {prop.name} is supported by statistical checking. Tea agrees with the user.")
                                else: 
                                    tea_logger.log_debug(f"User asserted property: {prop.name}, but is NOT supported by statistical checking. Tea will override user assertion.")
                                solver.add(ap.__z3__ == z3.BoolVal(val))
                            elif MODE == 'relaxed': 
                                tea_logger.log_debug(f"Running under RELAXED mode.")
                                if val: 
                                    tea_logger.log_debug(f"User asserted property: {prop.name} is supported by statistical checking. Tea agrees with the user.")
                                else: 
                                    tea_logger.log_debug(f"User asserted property: {prop.name}, but is NOT supported by statistical checking. User assertion will be considered true.")
                                solver.add(ap.__z3__ == z3.BoolVal(True)) # override user
                            else: 
                                raise ValueError(f"Invalid MODE: {MODE}")
        else:
            pass
    return assumed_props


# Helper for synthesize tests
def is_assumed_prop(assumed_props, prop):
    for ap in assumed_props:
        if prop == ap: 
            return True
    
    return False


# Problem statement: Given a set of properties, tell me which tests are valid to run
# This is a concrete (rather than symbolic) problem 
# @param combined_data CombinedData object
# @returns list of Property objects that combined_data exhibits
def synthesize_tests(dataset: Dataset, assumptions: Dict[str,str], combined_data: CombinedData):
    reset_all_tests()
    
    tea_logger = TeaLogger.get_logger()
    construct_all_tests(combined_data)

    global name
    stat_var_map = {}

    # Reorder variables so that y var is at the end
    combined_data._update_vars() 

    # Compute unique statisical variable names from the combined data.
    combined_data_vars = []
    for v in combined_data.vars:
        var = StatVar(v.metadata[name])
        stat_var_map[v.metadata[name]] = var 
        combined_data_vars.append(var)

    # Assume properties based on user assumptions and mode
    solver = z3.Solver()
    # s = Tactic('qflia').solver()
    assumed_props = assume_properties(stat_var_map, assumptions, solver, dataset, combined_data)
    # import pdb; pdb.set_trace()

    # Update the arity of test-level properties
    for prop in test_props: 
        prop._update(len(combined_data.vars))

    # Apply all tests to the variables we are considering now in combined_data
    for test in all_tests(): 
        test.apply(*combined_data_vars)

    solver.push() # Create backtracking point
    model = None # Store model

    # For each test, add it to the solver as a constraint. 
    # Add the tests and their properties
    for test in all_tests():
        tea_logger.log_debug(f"\nCurrently considering {test.name}")
        solver.add(test.__z3__ == z3.And(*test.query()))
        # import pdb; pdb.set_trace()
        solver.add(test.__z3__ == z3.BoolVal(True))

        # Check the model 
        result = solver.check()
        if result == z3.unsat:
            tea_logger.log_debug("Test is unsat.\n")
            solver.pop() 
        elif result == z3.unknown:
            print("failed to solve")
            try:
                pass
            except z3.Z3Exception:
                return
        else:
            model = solver.model()
            test_invalid = False
            val = False
            # Does the test apply?
            # Would this ever be false??
            if model and z3.is_true(model.evaluate(test.__z3__)):
                # Verify the properties for that test
                for prop in test._properties:
                    if is_assumed_prop(assumed_props, prop):
                        tea_logger.log_debug(f"User asserted property: {prop._name}.")
                        val = True
                        solver.add(prop.__z3__ == z3.BoolVal(val))
                    else: 
                        tea_logger.log_debug(f"Testing assumption: {prop._name}.")
                    
                        # Does this property need to hold for the test to be valid?
                        # If so, verify that the property does hold
                        if model and z3.is_true(model.evaluate(prop.__z3__)):
                            val = verify_prop(dataset, combined_data, prop)
                            if val: 
                                tea_logger.log_debug(f"Property holds.")
                            else: # The property does not verify
                                assert (val == False)
                                tea_logger.log_debug(f"Property FAILS")
                                # if not test_invalid: 
                                solver.pop() # remove the last test
                                test_invalid = True
                                model = None
                                # else: # test is already invalid. Going here just for completeness of logging
                                #     tea_logger.log_debug(f"EVER GET HERE?")
                            solver.add(prop.__z3__ == z3.BoolVal(val))
        solver.push() # Push latest state as backtracking point


        
        
    solver.check()
    model = solver.model() # final model
    tests_to_conduct = []
    # Could add all the test props first 
    # Then add all the tests 
    for test in all_tests():
        if model and z3.is_true(model.evaluate(test.__z3__)):
            tests_to_conduct.append(test.name)
        elif not model: # No test applies
            pass

    # reset_all_tests()
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
        # import pdb; pdb.set_trace()
        print("no solution")
    elif result == z3.unknown:
        print("failed to solve")
        try:
            # print(s.model())
            print(f"Failed to solve: {s.model()}")
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