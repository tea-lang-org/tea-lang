


# Last updated: 

# Paper: Suh & Hsieh, 2016

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
4. Specifying models
5. Declaring (and testing) hypotheses involving variables - must have models

- 6. Definitions of groups
- 7. Defining new composite variables based on other variables
- 8. Define order of ordinal data
- >, <, >=, <=, * (to mean interaction and multiplication)
- is, and (for querying/selecting data from dataset)

# Keywords
For exploratory data analysis, "explore" (necessary?)
"increases", "decreases", "as" OR "if"/"then"



# Function declarations
1. Reading data
load data: {
    name: 'dataset'
    source: '.csv'
    (8.) order: {
        variable: 'education'
        levels: 'high school', 'college', 'Master\'s', 'PhD'
    },
    {
        variable: 'rank'
        levels: 'lieutenant', 'captain','manager'
    }
}

2. [Exploratory analysis] Getting summary statistics for a variable
explore summary: {
    variable: 'age'
    characteristics: 'distribution', 'residuals', 'variance'/'heteroscedasticity',
                    'mean', 'median', 'stdev', 'variance'
}

3. [Exploratory analysis] Comparing properties for categorical variables
explore comparison: {
    groups: 'gender'
    outcome: 'NFC'
    select: 'task' is 'arithmetic'
}

(6.) explore comparison: {
    groups: {
        'young': 'age' <= 14
        'old': 'age' > 14
    }
    outcome: 'NFC'
}

#Edge case? : Outcome only necessary if Groups is not categorical??
# (see line 153 in hypotheses.py)
explore comparison: {
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

4. Specifying models
# All should be implemented as regression? or GLM?
model: {
    name: 'BI model' # if we want to allow declaration of models
    type: 'logistic regression' # should be deduced
    outcome: 'BI'
    predictors: 'AT', 'SN', 'PBC', 'SN'*'PBC'
}

model: {
    name: 'time model'
    between_subjects: 'task_type'
    within_subjects: 'microtask', 'interrupted'
    outcome: 'task_time'
    factors: 'task_type','microtask', 'interrupted', 'task_type'*'microtask', 'task_type'*'interrupted', 'microtask'*'interrupted', 'task_type'*'microtask'*'interrupted'
}

5. Declaring and testing hypotheses
test hypothesis: {
    model: 'BI model'
    prediction: as 'time' increases 'intention' decreases
    OR
    prediction: if 'time' increases then 'intention' decreases # more "elementary"
    # should only work for ORDINAL, INTERVAL, RATIO? 
}

test hypothesis: {
    iv: 'microtask' # variable we are testing
    dv: 'task_time'
    model: 'time_model' OR 
    model: {}
    prediction: 'microtask':1 > 'microtask':0 OR # if categorical
    prediction: as 'age' increases 'task_time' decreases # if numeric
}
# IF want to use same model for multiple hypotheses, have to declare test hypothesis or include multiple predictions!

test hypothesis: {
    iv: 'microtask'
    dv: 'preference'
    prediction: 'microtask':1 != 'microtask':0 # Preference will differ in some way
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
composite: {
    name: 'positive_affect'
    from: 'happy', 'joy', 'surprise', 'calm', 'sad'
    how: sum { # optional
        reverse: 'sad'
        min: 1
        max: 7
    }
}


Sample program: 
load data: {},
explore summary: {}, 
explore comparison: {},
model: {}, 
test hypothesis: {}

## QUESTIONS
# Should we have persistent memory (similar to R) where variables and models can be reused? 
