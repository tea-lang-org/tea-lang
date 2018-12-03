# Last updated: 

# Primitive Data Structure
variable
operation/function (statistical procedure or test)

# Primitive Data Types
Nominal 
Ordinal 
Interval
Ratio 
Functions

# Key Functions
1. Reading data 
2. Getting summary statistics for a variables
(3. Comparing properties for categorical variables - including t-tests)
4. Specifying models (mostly linear regression)
5. Declaring (and testing) hypotheses involving variables - must have models

- 6. Definitions of groups: # A special case of composites?
- 7. Defining new composite variables based on other variables: # Aggregates quantities based on sub-quantities
- 8. Define order of ordinal data (and nominal data)
- >, <, >=, <=, !=, ==, * (to mean interaction and multiplication?), other arithmetic for creating composites?
- is/==, and (for querying/selecting data from dataset)

# Keywords
For exploratory data analysis, "explore" (necessary?)
For specifying predictions: "increases", "decreases", "as" OR "if"/"then" (data type dependent)
For filtering data: "where" 

Sample program: 
load data: {},
explore summary: {}, 
explore comparison: {},
model: {}, 
test hypothesis: {}

# TO IMRPOVE
# - nominal data that is encoded as numbers

# Function declarations
1. Reading data
load data: {
    name: 'dataset'
    source: '.csv'
    order: {
        variable: 'education' (these are column names)
        type: 'ordinal'
        levels: 'high school', 'college', 'Master\'s', 'PhD'
    },
    {
        variable: 'rank'
        type: 'ordinal'
        levels: 'lieutenant', 'captain','manager'
    },
    {
        variable: 'gender'
        type: 'nominal'
        levels: 0, 1, 2
    }
}

2. [Exploratory analysis] Getting summary statistics for a variable
# univariate analyses
explore summary: {
    variable: 'age'
    characteristics: 'distribution', 'residuals', 
                    'mean', 'median', 'stdev', 'variance', 'histogram', 'outliers'
    characteristics: 'distribution', 'mean'
}

3. [Exploratory analysis] Comparing properties for categorical variables
explore/test comparison: {
    groups: 'gender'
    outcome: 'NFC'
    characteristics: 'homoscedasticity', 'multicollinearity', 
    filter/select: 'task' is 'arithmetic' 
    #'intercorrelation matrix' -- as output?
}

(6.) explore comparison: {
    # concern with binning: skewed data --> Warning
    # Class imbalance and power??
    # Data-driven vs. domain knowledge-driven
    groups: {
        'young': 'age' <= 'age':'median' or 'median', 'quantiles'
        'old': 'age' > 14 # explicit value declaration
    }
    outcome: 'NFC'
}

4. Specifying models
# All should be implemented as regression? or GLM?
model: {
    name: 'BI model' # if we want to allow declaration of models
    type: 'logistic regression' # should be deduced && cause warning if problematic
    dv: 'BI'
    iv: 'AT', 'SN', 'PBC', 'SN'*'PBC'
    direction: 'forward', 'backward'
    # In interactions: Are individual factors put in ; order
}

# TODO "experiment" or "conditions" or 
design experiment: {
    name: 'task experiment'
    between_subjects: 'task_type'
    within_subjects: 'microtask', 'interrupted'
}

#var 'time model' = {}
model: {
    name: 'time model'
    experiment: 'task experiment'
    #between_subjects: 'task_type'
    #within_subjects: 'microtask', 'interrupted'
    dv: 'task_time'
    iv: 'task_type','microtask', 'interrupted', 'task_type'*'microtask', 'task_type'*'interrupted', 'microtask'*'interrupted', 'task_type'*'microtask'*'interrupted'
}

5. Declaring and testing hypotheses
test hypothesis: {
    model: 'time model'
    prediction: as 'time' increases 'intention' decreases
    OR
    prediction: if 'time' increases then 'intention' decreases # more "elementary"
    # should only work for ORDINAL, INTERVAL, RATIO? 
}

# bivariate analyses vs coefficient in model
# dependence of the variables
test hypothesis: {
    iv: 'microtask' # variable we are testing
    dv: 'task_time'
    # "in the context of model" is optional (different from testing hypothesis in context of model)
    model: 'time_model' OR 
    model: {}
    # More verbose representation:

    # prediction: 'microtask':1 > 'microtask':0 OR # if categorical
    # prediction: 'task_time' - when 'microtask' is 1  > when 'microtask' is 0
    # prediction: if 'microtask' is 1 then 'task_time' >
   # prediction: 'task_time' where/when/if 'microtask' is 1 > 'task_time' where/when/if 'microtask' is 0 # error if output variables and conditions not matched
    #prediction: 'task_time' where 'microtask' is 'elephat' >> 'task_time' where 'microtask' is not 'elephant'  

    prediction: 1 > 0 # easier for partial orders
    prediction: 3 > 2, 2 > 1, 3 > not 3, 3 != not 3, 3 >> VERY VERY LARGE # easier for partial orders
    prediction: 'microtask' is 1 > 'microtask' is 0
    
}
# IF want to use same model for multiple hypotheses, have to declare test hypothesis or include multiple predictions!

test hypothesis: {
    iv: 'microtask' # variable we are testing
    dv: 'task_time'
    model: 'age_model'
    prediction: as 'age' increases 'task_time' decreases # if numeric
}

test hypothesis: {
    iv: 'microtask'
    dv: 'preference'
    prediction: 'microtask':1 == 'microtask':0 # Preference will differ in some way
    # specifying the null hypothesis? How do we test null hypothesis?

    # Null hypothesis
    # Detect directional difference >,< -- 1 vs. 2-tailed tests
    # 2-tailed tests first then 1-tailed test after? -- Which warnings to raise? Might be more of a user issue
    # Ask a statistician!
}

# Predictions can have a slight query-like nature 
# Testing how microtasks (iv) affect perceived load (dv)
test hypothesis: {
    iv: 'microtask'
    dv: 'NASA_TLX'
    model: 'preference model'
    prediction: 'task_type':arithmetic and 'microtask':1 < 'task_type':arithmetic and 'microtask':0
    prediction: 'task_type':sorting and 'microtask':1 < 'task_type':sorting and 'microtask':0
    prediction: 'task_type':transcription and 'microtask':1 < 'task_type':transcription and 'microtask':0
}

7. Defining composites # how would I use this in the other functions??
## ONLY WORKS FOR INTERVAL/RATIO DATA
composite/aggregate: {
    name: 'positive_affect'
    from: 'happy', 'joy', 'surprise', 'calm', 'sad'
    how: sum/count { # sum is more common?
        reverse: 'sad'
        min: 1
        max: 7
    }
}

# "Allow by not require" -- show visualizations throughout Explore & also support customization
# QQPlot
# "Interesting visualizations" related to Warnings? timing of visualizations
visualize: {
    hypothesis: 'time model'
    # Picks best graph to represent hypothesis? (How would this even be possible?)
}
visualize: {
    x: nest 'interruption' in 'microtask'
    y: 'task_time'
    nest: color # how show nested nature? using color
}


#Edge case? : Outcome only necessary if Groups is not categorical??
# (see line 153 in hypotheses.py)
explore comparison: {
    # Maybe name this column group or some other name??
    groups: {
        composite: {
            name: 'micro_time'
            from: 'micro_arithmetic_time','micro_sorting_time','micro_transcription_time'
            how: mean # sum, mean, median (most common?)
        },
        composite: {
            name: 'macro_time'
            from: 'macro_arithmetic_time','macro_sorting_time','macro_transcription_time'
            how: mean
        }
    }
}

## QUESTIONS
# Should we have persistent memory (similar to R) where variables and models can be reused? 
# Output 
# Visualization: - always include visualizations?, could be a separate step to specifiy visualizations?
#               - implementation: feed into vega-lite
#               - customization: visualization be a separate step 