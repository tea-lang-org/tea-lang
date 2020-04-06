# [WIP] Tea Documentation

Tea is a domain specific programming language that automates statistical test
selection and execution. Tea is currently written in/for Python. 

Tea has an <a href='http://tea-lang.org/index_files/tea_UIST2019.pdf'>academic research paper</a>. 

<a href='https://pypi.org/project/tealang/'>Tea is available on pip!</a>
```
pip install tealang
```

Tea can be easily integrated into Python... 
```
import tea
```

## How do I write a Tea program?

Users provide 5 pieces of information: 
* the *dataset* of interest, 
* the *variables* in the dataset they want to analyze, 
* the *study design* (e.g., independent, dependent variables),
* the *assumptions* they make about the data based on domain knowledge, and
* a *hypothesis*.

Let's unpack each of these in detail...

### Dataset
Tea accepts data either as a CSV or a Pandas DataFrame. Tea assumes data is in 
<a href='http://www.cookbook-r.com/Manipulating_data/Converting_data_between_wide_and_long_format/'>"long format."</a>

Optional: a column in the dataset can be designated as a relational (or primary) key. 
This key should be an attribute that uniquely identifies rows of data. Including a key is 
helpful if, for example, participants have multiple entries, as in a within-subjects study.
If no key is included, then all rows are treated as individual observations, i.e. all 
variables are between-subjects.

### Variables
Variables correspond to columns given in the dataset. Only the columns of interest 
need to be indicated as variables. Users describe a variable by including its column *name*, 
its *data type*, and any additional information.  

Tea recognizes three data types: *nominal*, *ordinal*, and *numeric*.

A variable is *nominal* if its values represent discrete categories, and *ordinal* if 
these categories are ordered. These *categories* should be included in the variable description.

A variable is *numeric* if it represents continuous values. A optional *range* can be 
included.

### Study Design

Users specify their study design by including the study type as well as the 
relevant variables of interest.

Tea supports 2 kinds of studies: *observational* and *experiment*.

For an experiment, users describe *independent variables* and *dependent variables*.
 
For an observational study, users specify *contributor variables* and 
*outcome variables*. 

Multiple variables can be included as a list.

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
Tea currently supports Null Hypothesis Significance Testing (NHST), which tests the observations 
in the dataset against the hypothesis that they occurred by random chance, not as the result 
of a relationship between the specified variables. 

By default, Tea uses the null hypothesis that there is no relationship between variables.

Users can specify alternative hypotheses by providing variables of interest, 
as well as formulating the hypothesized relationship between those variables. Each 
hypothesis should have exactly one dependent variable, but may have multiple independent 
variables.

## How do I interpret the output of my Tea program?

At runtime, Tea "compiles" these 5 pieces of information into logical constraints 
to select valid statistical tests. Tests are considered valid if and only if *all* the
assumptions they make about the data (e.g., normal distribution, equal
variance between groups, etc.) hold. Tea outputs its decision process for every 
statistical test it considers.

Tea then selects and executes the tests whose assumptions hold. The results are displayed 
as output as well as returned by Tea's `hypothesize()` function. For each test, the 
results include the name of the test, its assumptions about the variables, and the 
calculated statistics, which (depending on the particular test) may include:

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