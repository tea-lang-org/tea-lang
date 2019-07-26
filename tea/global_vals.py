# Contains all the global values referenced throughout Tea

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

# LOGGING
# TODO: This shoudl eventually write out to a file somewhere.
def log(message: str):
    print(message)
    # pass

# Test names.
pearson_name = "Pearson Correlation"
kendalltau_name = "Kendall\'s Tau Correlation"
spearman_name = "Spearman\'s R Correlation"
pointbiserial_name = "Pointbiserial Correlation"
students_t_name = "Student\'s T Test"
paired_students_name = "Paired Student\'s T Test"
welchs_t_name = "Welch\'s T Test"
mann_whitney_name = "Mann Whitney U Test"
wilcoxon_signed_rank_name = "Wilcoxon Signed Rank Test"
rm_one_way_anova_name = "Repeated Measures One Way ANOVA"
factorial_anova_name = "Factorial ANOVA"
kruskall_wallis_name = "Kruskall Wallis"
f_test_name = "F Test"
chi_square_name = "Chi Square Test"
fisher_exact_name = "Fisher\'s Exact Test"
