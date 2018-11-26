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


