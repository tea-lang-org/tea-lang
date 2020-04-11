# [WIP] Tea Documentation

Tea is a domain specific programming language that automates statistical test
selection and execution. Tea is currently written as an open-source Python library
for integration into data analysis workflows using Python (3.6 or higher). 

Tea is designed for non-statistical experts who want to perform statistical analyses 
within their specific domain of expertise. If this is you, you're in the right
place :) Let's get started!

<a href='https://pypi.org/project/tealang/'>Tea is available on pip!</a> You can
install Tea by typing the following terminal command into your console:
```
pip install tealang
```

Then, open whatever IDE you use for Python, and create a new Python file.
Make sure to add an import statement so that you'll have Tea ready to use
in your file:
```
import tea
```

You're all set! The next section will walk you through the steps of writing 
your own program in Tea.

## How do I write a Tea program?

You'll want to provide Tea with 5 pieces of information: 
* the *dataset* of interest, 
* the *variables* you want to analyze,
* the *study design* (e.g., specifying independent, dependent variables),
* any *assumptions* you may have about the data based on domain knowledge, and
* a *hypothesis*.

Let's unpack each of these in detail...

### Dataset
Tea accepts data either as a CSV or a Pandas DataFrame. Tea assumes data is in 
<a href='http://www.cookbook-r.com/Manipulating_data/Converting_data_between_wide_and_long_format/'>"long format."</a>

```
data_path = "./athlete_events.csv"
tea.data(data_path)
```

##### Designating a key:

Optionally, you may want a column in the dataset to serve as a relational (a.k.a. primary) key. 
This key should be an attribute that acts as a row identifier.

If no key is included, then all rows are treated as individual observations, i.e. all 
variables are between-subjects.

Including a key is helpful when participants have multiple entries in the dataset, i.e.
as for a within-subjects study.

To specify a key, simply add an argument when passing the dataset to Tea:

```
tea.data(data_path, key='ID')
```

The value included as the key name (`'ID'` in the example above) should be the name 
of a *variable* that you define from the dataset.

### Variables
Variables correspond to columns given in the dataset. You only need to define variables 
for the attributes of interest; it's fine to have columns in the dataset that are not
actually used in your Tea program.
 
You can describe a variable by including its column *name* and its *data type*.
Depending on the data type, you'll also need to include additional information.

##### Defining data types:

Tea recognizes three data types: *nominal*, *ordinal*, and *numeric*.

A variable is *nominal* if its values represent discrete categories, and *ordinal* if 
these categories are ordered. These *categories* should be included in the variable description.
```
{
    'name' : 'Condition',
    'data type' : 'nominal',
    'categories' : ['AR', 'TV']
},
{
    'name' : 'Score',
    'data type' : 'ordinal',
    'categories' : [1,2,3,4,5]
}
```

A variable is *numeric* if it represents continuous values. A optional *range* can be 
included.
``` 
{
    'name' : 'Prob',
    'data type' : 'numeric',
    'range' : [0,1]             # optional
}
```
##### Describing variables for Tea:
You'll want to define your variables as a list, which you can then pass to Tea:
``` 
variables = [
    {
        'name' : 'Condition',
        'data type' : 'nominal',
        'categories' : ['AR', 'TV']
    },
    {
        'name' : 'Score',
        'data type' : 'ordinal',
        'categories' : [1,2,3,4,5]
    }
]
tea.define_variables(variables)
``` 

### Study Design

Next, you'll specify your study design by including the type of the study as well as the 
relevant variables of interest.

Tea supports 2 kinds of studies: *observational study* and *experiment*.

##### Specifying an observational study:
For an observational study, you should describe *contributor variables* and 
*outcome variables*. 
``` 
experimental_design = {
    'study type': 'observational study',
    'contributor variables': 'Sport',
    'outcome variables': 'Weight',
}
tea.define_study_design(study_design)
```

##### Specifying an experiment
For an experiment, you should describe *independent variables* and *dependent variables*.
``` 
study_design = {
    'study type': 'experiment',
    'independent variables': 'Condition',
    'dependent variables': 'Score'
}
tea.define_study_design(study_design)
```
##### Including multiple variables
If you'd like, multiple variables can be specified as a list. For example: 
``` 
experimental_design = {
    'study type': 'observational study',
    'contributor variables': ['Sport', 'Sex'],
    'outcome variables': 'Weight',
}
tea.define_study_design(study_design)
```
This can be useful if you're planning to test several hypotheses using different attributes.

### Assumptions
Domain knowledge can be provided to Tea explicitly via the `assume()` function.
These assumptions are optional and are not required for a valid Tea program.

First, users can describe assumptions about variables' statistical properties (e.g.,
a variable is normally distributed). Tea checks these assumptions and issues warnings 
for those that are not verified by statistical testing. 
To specify how Tea should handle these cases, users can select one of two modes: *strict* (default) or *relaxed*. In *strict* mode, 
Tea will override user assumptions if they are determined unverifiable. In *relaxed* 
mode, Tea will proceed with all user assumptions regardless of whether or not they
are verified.

As part of the assumptions, users can also specify the *Type I (False Positive) Error 
Rate*, or the alpha value, which represents the threshold p-value at which the null 
hypothesis should be rejected. The default alpha value is 0.05.

The assumptions can also include any known data transformations (i.e., log 
transformation) that apply to a variable.

### Hypothesis

You can write hypotheses in Tea by specifying the variables of interest, 
then formulating the hypothesized relationship between those variables.

##### Describing different hypothesis types
Tea currently allows you to express the following range of hypotheses:
* One-sided comparison between groups
```
tea.hypothesize(['Region', 'Imprisonment'], ['Region: Southern > Northern']) 
```
Here, `Region` is the name of a *nominal* or *ordinal* variable that has `Southern` 
and `Northern` as *categories*. This hypothesis describes a higher rate of `Imprisonment` 
(an *ordinal* or *numeric*) variable in the `Southern` category compared to the `Northern`
category.

* Partial orders
```
tea.hypothesize(['Region', 'Imprisonment'], ['Region: Southern > Southwest, Region: Northeast > Midwest']) 
```

* Two-sided comparisons
```
tea.hypothesize(['Region', 'Imprisonment'], ['Region: Southern != Northern']) 
```

* Positive linear relationships
```
tea.hypothesize(['Region', 'Imprisonment'], ['Imprisonment ~ +Region']) 
```
If no +/- sign is included, Tea will treat the hypothesis as a positive linear 
relationship by default.

* Negative linear relationships
```
tea.hypothesize(['Region', 'Imprisonment'], ['Imprisonment ~ -Region']) 
```

##### Providing multiple hypotheses
As long as all variables of interest are defined and included in the study design,
you can specify as many hypotheses as you'd like:
``` 
results_1 = tea.hypothesize(['Sport', 'Weight'], ['Sport:Wrestling < Swimming'])
results_2 = tea.hypothesize(['Sex', 'Weight'], ['Sex:F < M'])
```

##### Testing against the Null Hypothesis
Tea currently supports Null Hypothesis Significance Testing (NHST), which tests *your* 
hypothesis&mdash;that there is some relationship between certain variables in your dataset&mdash;
against a *null hypothesis*.

By default, Tea uses the null hypothesis that there is no relationship between variables, i.e. 
the data in your dataset occurred by random chance.

The statistical tests selected by Tea will determine whether the null hypothesis should 
be accepted or rejected, i.e. whether you can conclude that there is indeed a relationship   
between the variables specified in your hypothesis.

## How do I interpret the output of my Tea program?

At runtime, Tea "compiles" the above 5 pieces of information into logical constraints, 
which it uses to select and execute a set of valid statistical tests for testing your hypothesis.

##### Selecting valid tests
A test is considered valid if and only if *all* the assumptions it makes about 
the data (e.g., normal distribution, equal variance between groups, etc.) hold.

Tea outputs its decision process for every statistical test it considers.

Here's an example of what the output could look like for a statistical test 
that Tea finds to be *invalid*:
```
Currently considering kendalltau_corr
Testing assumption: is_bivariate.
Property holds.
Testing assumption: is_continuous_or_ordinal.
Property FAILS
```
Once Tea checks a certain assumption, it remembers whether or not that property 
holds. This allows Tea to more quickly evaluate other tests that require the same 
assumption(s). For instance, the following test was directly deemed unsatisfiable 
because Tea had already found that its properties failed: 
```
Currently considering spearman_corr
Test is unsat.
```
A *valid* statistical test would have output showing that all required 
assumptions are satisfied:
```
Currently considering mannwhitney_u
Testing assumption: has_one_x.
Property holds.
Testing assumption: has_one_y.
Property holds.
Testing assumption: has_independent_observations.
Property holds.
Testing assumption: is_categorical.
Property holds.
Testing assumption: has_two_categories.
Property holds.
Testing assumption: is_continuous_or_ordinal.
Property holds.
```

##### Executing valid tests
The moment you've been waiting for... once Tea has found a set of valid statistical tests,
it will execute each one to test your hypothesis!

These results are displayed as output as well as returned by Tea's `hypothesize()` function. For each test, the 
results include the name of the test, its assumptions about the variables, and the 
calculated statistics.

For example, the results of executing the Mann Whitney U Test would look something 
like this:
``` 
***Test results:
name = Mann Whitney U Test
test_statistic = 75231500.50000
p_value = 0.00000
adjusted_p_value = 0.00000
alpha = 0.05
dof = 23195
Effect size:
A12 = 0.55642
Null hypothesis = There is no difference in medians between Sport = Swimming and Sport = Wrestling on Weight.
Interpretation = t(23195) = 75231500.50000, p = 0.00000. Fail to reject the null hypothesis at alpha = 0.05. There is no difference in medians between Sport = Swimming and Sport = Wrestling on Weight.The effect size is A12 = 0.55642. The effect size is the magnitude of the difference, which gives a holistic view of the results [1].
[1] Sullivan, G. M., & Feinn, R. (2012). Using effect size—or why the P value is not enough. Journal of graduate medical education, 4(3), 279-282.
```

Depending on the particular test, the calculated values may include:
* test statistic:
* p-value: the probability of obtaining the given test results under the null hypothesis 
(i.e., if there is no relationship between the variables) 
* adjusted p-value:
* alpha: the level of significance for the p-value, or the threshold for accepting/rejecting 
the null hypothesis 
* degrees of freedom (dof): 
* Effect size (A12): the magnitude of the difference, which gives a holistic view of the results 

Tea then states whether or not the null hypothesis should be rejected based 
on the results from that particular test execution.
 

## How does Tea decide which statistical analysis tests to run?
Diagram of the internals. Flow chart? Table format? Dynamic vs. static?
This may be tricky because the exact process is data-dependent.