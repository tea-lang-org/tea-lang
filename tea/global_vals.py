# Contains all the global values referenced throughout Tea

NOMINAL= "nominal"
ORDINAL = "ordinal"
NUMERIC = "numeric"
INTERVAL = "interval" # for backwards compatibility
RATIO = "ratio" # for backwards compatibility

VARIABLE_NAME = "name"
VARIABLE_TYPE = "data type"
VARIABLE_CATEGORIES = "categories"
VARIABLE_ATTRS = [VARIABLE_NAME, VARIABLE_TYPE, VARIABLE_CATEGORIES]

STUDY_TYPE = "study type"
OBS_X = ["contributor variable", "contributor variables"]
OBS_Y = ["outcome variable", "outcome variables"]
EXP_X = ["independent variable", "independent variables"]
EXP_Y = ["dependent variable", "dependent variables"]
OBS_STUDY = "observational study"
EXPERIMENT = "experiment"


# For study design dictionary
btw_subj = 'between subjects'
within_subj = 'within subjects'
uid = 'key'

study_type_identifier = 'study type'
experiment_identifier = 'experiment'
observational_identifier = 'observational study'
iv_identifier = 'independent variables'
dv_identifier = 'dependent variables'
null_identifier = 'variables'
outcome_identifier = 'outcome variables'
contributor_identifier = 'contributor variables'
#quasi_experiment = 'quasi_experiment'

# For statistical properties of data
normal_distribution = 'normal distribution'
groups_normal = 'groups normally distributed'
log_normal_distribution = 'log normal distribution'
variance = 'variance'
sample_size = 'sample size'
num_categories = 'number of categories'
eq_variance = 'equal variance'
paired = 'paired'
cat_distribution = 'category distributions'

# For non-statistical meta-properties of data
name = 'var_name'
data_type = 'dtype'
categories = 'categories'
query = 'query'

# For solver
# Maps assumption names (from user) to property names
alpha_keywords = ['Type I (False Positive) Error Rate', 'alpha']

assumptions_to_properties = {
    normal_distribution : ['is_normal'],
    groups_normal : ['is_groups_normal'],
    log_normal_distribution : ['is_log_normal'],
    eq_variance : ['has_equal_variance']
}

# For solver, how to treat user assumptions
# MODE = 'strict' #can be 'strict' or 'relaxed'