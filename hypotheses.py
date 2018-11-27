# Last updated: 
# Purpose: To test/try out different ways of writing out hypotheses for statsitical analysis



# Paper: Suh & Hsieh, 2016
"""
H1:  People  will  produce  more  attitude  beliefs  when  
considering    behaviors    in    
far    future    than    when    
considering behaviors in the near future.   
H2:   People   will   produce   more   perceived   behavior   
control   beliefs   wh
en   considering   behaviors   in   near   
future   than   when   considering   behaviors   in   the   far   
future. 


data: {
    name: 'dataset1'
    source: '.csv'
}

# H1
# test keyword indicates statistical test
## compare does the comparison that is possible with the given data types
test : {
    groups: 'time', median-split
    outcome: 'attitude_beliefs' # don't really need to explicitly state that this is continuous?
    prediction: 'time':Far > 'time':Near
}
____

hypothesis: {
    iv: 'time'
    dv: 'attitude_beliefs'
    prediction: 'time':Far > 'time':Near
}

#H2
# should use "test" with action word (e.g., compare)??
test compare: { 
    groups: 'time'
    outcome: 'perceived_beh_control'
    prediction: 'time':Near > 'time':Far
}
___

# when to call categorize??
categorize: {
    data : 'time'
    groups: {
        'Near': < 4
        'Far': >= 4
    }
}
hypothesis: {
    iv: 'time'
    dv:'preceived_beh_control'
    split: median OR mean (how to form 2 groups if Near/Far are not categorical datatypes)
    prediction: 'time':Near > 'time':Far
}

# What if want to compare the means of two groups without doing test? 
compare: {
    groups: 'time'
    outcome: 'perceived_beh_control'
    characteristic: 'mean', 'stdev' # all is the default
}

# Creating new composite variables
# should be agnostic to dataset? 
composite: {
    name: 'AT'
    from: 'instrumental', 'affective'
    how: sum
    # OR if there are reverse questions, as in surveys, etc.
    how: sum { 
        reverse: 'affective'
        min: 1
        max: 7
    }
}

H3:  AT  is  a  stronger  predictor  of  behavior  intention  in  
the far future than in the near future.  
H4: PBC is a stronger predictor of behavior intention in 
the near future than in the far future.  

# H3
test regression: {
    type: 'logistic' # should not be required and/or checked automatically...
    group: ''
    outcome: 'AT coeff'
    models: {
        outcome: 'BI'
        select: 'time':Near
        predictors: 'AT', 'SN', 'PBC'
    }, 
    {
        outcome: 'BI'
        select: 'time':Far
        predictors: 'AT', 'SN', 'PBC'
    }
    property: 'predictive power' OR 'Beta' # Beta coefficients in two different models
    prediction: '
}

# H4
similar to H3 -- not sure yet how to compare characteristics of models

# H5
hypothesis: {
    outcome: 'intention'
    group: 'temporal_distance'
    prediction: as group/'temporal_distance' decreases outcome/'intention' decreases # use increases and decreases as keywords
} # this might try to do a model but the authors only looked at static time points (month vs. few days vs. after event)
___
hypothesis: {
    iv: 'temporal_distance'
    dv: 'intention'
    prediction: as group/'temporal_distance' decreases outcome/'intention' decreases # use increases and decreases as keywords
}
summarize{dataset1}

"""

"""
Summarizing/creating compositive variables based on multiple questions (i.e., survey responses)
score: {
    composite: ''
    from: 'col_1', 'col_2', 'col_3'
    reverse: 'col_2' # reverse scoring for surveys/questions
    min: 1 # minimum score possible on the questions (could also deduce automatically?)
    max: 7 # 7-point Likert scale; this could be output to the user to confirm/verify/get feedback
}
"""

# Paper: Cheng et al. 2015
"""
# Time
# to be able to declare before/outside a function call, we would need to store data somewhere
define composite: {
    name: 'micro_time'
    from: 'micro_arithmetic_time', 'micro_sorting_time', 'micro_transcription_time'
    combine: sum
}
define composite: {
    name: 'macro_time'
    from: 'macro_arithmetic_time', 'macro_sorting_time', 'macro_transcription_time'
    combine: sum
}
compare: {
    ?? outcome: 'time'
    groups: ('micro_arithmetic_time', 'micro_sorting_time', 'micro_transcription_time') && ('macro_arithmetic_time', 'macro_sorting_time', 'macro_transcription_time') 
    groups: 'micro_'* # could allow for some shortcuts
    prediction: ('micro_arithmetic_time', 'micro_sorting_time', 'micro_transcription_time') > ('macro_arithmetic_time', 'macro_sorting_time', 'macro_transcription_time') 
    groups: 'micro', 'macro'
    prediction: 'micro'  > 'macro' 

    characteristic: 'mean'
    style: 'pairwise'
}

test compare: {
    groups: ('micro_arithmetic_time', 'micro_sorting_time', 'micro_transcription_time') && ('macro_arithmetic_time', 'macro_sorting_time', 'macro_transcription_time') 
    prediction: ('micro_arithmetic_time', 'micro_sorting_time', 'micro_transcription_time') > ('macro_arithmetic_time', 'macro_sorting_time', 'macro_transcription_time') 
}

compare: {
    groups: 'micro_arithmetic_time' && 'macro_arithmetic_time'
}

model: {
    between_subjects: 'task_type'
    within_subjects: 'microtask', 'interrupted'
    outcome: 'task_time'
    predictors: 'task_type', 'microtask', 'interrupted', 'task_type'*'microtask', 'task_type'*'interrupted', 'microtask'*'interrupted', 'task_type'*'microtask'*'interrupted'
}
___ 
define model: {
    name: 'model_time'
    between_subjects: 'task_type'
    within_subjects: 'microtask', 'interrupted'
    outcome: 'task_time'
    predictors: 'task_type', 'microtask', 'interrupted', 'task_type'*'microtask', 'task_type'*'interrupted', 'microtask'*'interrupted', 'task_type'*'microtask'*'interrupted'
}
hypothesis: {
    iv: 'microtask'
    dv: 'task_time'
    model: model_time OR 
    model :{ } # embed declaration in hypothesis declaration
    prediction: 'microtask':1 > 'microtask':0
} # this declaration does not know about other factors, repeated designs, etc. 

experimental_design: {
    between_subjects: 'task_type'
    within_subjects: 'microtask', 'interrupted'
}
hypothesis: {
    iv: 'microtask'
    dv: 'task_time'
    # model in hypothesis declaration is how hypothesis is tested, there are other default ways, too
    model: {} # still needs to define model....
} # if define experimental design first/within scope, program can analyze keeping these in mind?  -- 
  # in interactive version, could also surface suggestions for models dynamically?

# Error/Quality
model: {
    outcome: 'num_errors'
    # could declare BETWEEN/WITHIN in list of predictors
    # better to have explicit field for listing between and within because people forget
    # default should be to treat variables as between?
    predictors: 'task_type'BTW, 'microtask'WITH, 'interrupted'WITH, 'task_type'*'microtask', 'task_type'*'interrupted', 'microtask'*'interrupted', 'task_type'*'microtask'*'interrupted'
}

model: {
    between_subjects: 'task_type'
    within_subjects: 'microtask', 'interrupted'
    outcome: 'num_errors'
    predictors: 'task_type', 'microtask', 'interrupted', 'task_type'*'microtask', 'task_type'*'interrupted', 'microtask'*'interrupted', 'task_type'*'microtask'*'interrupted'
}
___

model: {
    between_subjects: 'task_type'
    within_subjects: 'microtask', 'interrupted'
    dv: 'num_errors'
    iv: 'task_type', 'microtask', 'interrupted', 'task_type'*'microtask', 'task_type'*'interrupted', 'microtask'*'interrupted', 'task_type'*'microtask'*'interrupted'
}
hypothesis: {
    iv: 'microtask'
    dv: 'num_errors'
    model: {} (above)
    prediction: 'microtask':1 < 'microtask':0 # Microtasks will have fewer errors than macrotasks
}

# Preference 1
compare: {
    groups: 'microtask'
    outcome: 'preference'
} OR 
summarize: {
    'preference' # do all or some set of standard comparisons where 'preference' is involved??? (too many possibilities)
}
___ 
hypothesis: {
    iv: 'microtask'
    dv: 'preference'
    prediction: 'microtask':1 != 'microtask':0 # Preferences will be different in some way
}

# Preference 2
compare: {
    outcome: 'NASA_TLX'
    groups: 'microtask', 'task_type'*'microtask' # interaction appropriate??
}
___
hypothesis: {
    iv: 'microtask'
    dv: 'NASA_TLX'
    prediction: 'microtask':1 != 'microtask':0 # Preferences will be different in some way
}

# Can hypothesis have more than one prediction???
hypothesis: {
    iv: 'microtask'
    dv: 'NASA_TLX'
    compare-within: 'task_type' # is this even necessary if specify in predictions??
    # Maybe the predictions have a slight query-esque property???
    prediction: 'task_type':arithmetic and 'microtask':1 < 'task_type':arithmetic and 'microtask':0
    prediction: 'task_type':sorting and 'microtask':1 < 'task_type':sorting and 'microtask':0
    prediction: 'task_type':transcription and 'microtask':1 < 'task_type':transcription and 'microtask':0
    # how convey interaction effect prediction?????
}

# Interruptions
compare: {
    outcome: 'time'
    group: 'microtask'
    select: 'task_type' is 'arithmetic' # "select" or "filter" or ...
    model: 't-test' # optional
}

summarize: {
    variable: 'distractor_time'
    characteristic: 'mean'
}
___
hypothesis: {
    iv: 'microtask'
    dv: 'time'
    select: 'task_type' is 'arithmetic'
}
#...what if...
compare: {
    group: 'microtask'
    outcome: 'time'
    select: 'task_type' is 'arithmetic'
}

hypothesis: {
    name: 'time model'
    iv:'microtask'
    dv: 'time'
    model: compare 
    prediction:'microtask':1 != 'micortask':0
}
# Hypothesis and compare do similar things/backend but the "language" is different
# Predictions are necessary for hypothesis
# Maybe only hypotheses give statistical tests???

# Visualizing the graphs
visualize: {
    hypothesis: 'time model'
    # Picks best graph to represent hypothesis? (How would this even be possible?)
}
visualize: {
    x: nest 'interruption' in 'microtask'
    y: 'task_time'
    nest: color # how show nested nature? using color
}
"""
