#Clang -f sanitize=address

## CONFOUNDED DATA COLLECTION (PL and bugs)
# --> Suggest possible confounds?
# Visualization guides analysis/Analysis guides visualization
# Start with question have
# Data imbalance
# Require stating actually testing for (formulating)
# - formulate as experiment AND formulate as statistical analysis
# Synthesize precise text from experiemnt/stats doing -- compare with research question

# NEXT STEP:
- express hypothesis in different ways
- Guidelines in order of checklist about data

# Error messages and how to tell users: next layer - e.g., Did you mean to do X?

"""
data: '.csv' -- possibly could read in other data file types

summarize: 'data_fun' -- use column name
compare: {
    groups: 'satisficing'
    outcome: 'data_bored', 'data_fun', 'data_science', 'data_compare' , 'data_selfLearn'
    between_subjects: bool -- default is between
    within_subjects: bool -- should check automatically?
}
check: {
    characteristic: 'distribution' // any characteristic spat out by summarize
}
generalize: {
    predictors: 
}
visualize: {
    type: '' -- bar, line, plot, etc.
    x: ''
    y: ''
}
"""

"""
data: '.csv'

what-is: mean, 'column_name'
what-is: data_type, 'column_name'
what-is: distribution, 'column_name'
what-is: summary, 'column_name' # all the characteristics
what-is: outlier, 2, 'column_name' # 2 standard deviation

can-do: t-test, 'x', 'y'
can-do: chi-square, 'x', 'y'

why can-do: t-test, 'x', y'


visualize: histogram, 'column_name'
visualize: plot, 'x', 'y'

what-if: mean=9, 'column_name'
"""

"""
data: '.csv'

define outlier = 2 sd
define outlier = 3 sd

what-is: outlier, 'column_name' # use definition/specification of outlier
"""

"""
data: '.csv' # read some data in somehow
exclude-data :{
    when: 'always' || 'intelligently'
    what: 'NA' in 'col_name', 'col_name'
    what: '[none]' in 'col_name', 'col_name'
}

# more "data-minded"
data-check: {
    data: 'column_name'
    characteristic: 'distribution'
    expected: 'NORMAL' || 'POSITIVE SKEW' || 'NEGATIVE SKEW' || 'SKEW"
}

## IF THERE IS MISSIN DATA - COULD EXPRESS/CHECK INTERACTIONS
# more "experiment-minded"
hypothesis: {
    iv: 'condition_col'
    dv: 'outcome_col'
    direction: 'condition_col':'Condition1' > 'condition_col':'Condition2' # greater
    direction: 'condition_col':'Condition1' != 'condition_col':'Condition2' # not equal/different
    # ^ should allow autocompleting
}
hypothesis: {
    iv: 'data_fun', 'data_compare', 'data_bored'
    dv: 'dropout'
    groups: 'study'
    distribution: 'binomial' # optional -- could deduce
    model: 'chi-square' # optional
    model: 'linear regression' # optional -- the language/program should do the tests that are most appropriate
}
hypothesis: {
    iv: 'data_fun', 'data_compare' , 'data_bored'
    dv: 'performance'
    select-only: 'study' == 'visual preferences' # maybe this isn't even needed. Program can deduce
}
"""


""" THOUGHTS
1. Are we creating a wrapper around existing libraries/languages?
If so, what differentiates us from being yet another library?
2. User group (not statistically sophisticated) - how much expressivity?
3. What are the requirements of this language?
 - readable (code and output)
 - expressive (how much automation?)
 - 
4. User groups/personas?
"""