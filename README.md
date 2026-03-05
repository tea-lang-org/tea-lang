# tea-lang [![CI](https://github.com/tea-lang-org/tea-lang/actions/workflows/ci.yml/badge.svg)](https://github.com/tea-lang-org/tea-lang/actions/workflows/ci.yml)

# Tea: A High-level Language and Runtime System for Automating Statistical Analyses

## What is Tea?
Tea is a domain specific programming language that automates statistical test
selection and execution. Tea is currently written in/for Python. 

Tea has an <a href='http://tea-lang.org/index_files/tea_UIST2019.pdf'>academic research paper</a>. 

Users provide 5 pieces of information: 
* the *dataset* of interest, 
* the *variables* in the dataset they want to analyze, 
* the *study design* (e.g., independent, dependent variables),
* the *assumptions* they make about the data based on domain knowledge(e.g.,
a variable is normally distributed), and
* a *hypothesis*.

Tea then "compiles" these into logical constraints to select valid
statistical tests. Tests are considered valid if and only if *all* the
assumptions they make about the data (e.g., normal distribution, equal
variance between groups, etc.) hold. Tea then finally executes the valid tests.

## What kinds of statistical analyses are possible with Tea?
Tea currently provides a module to conduct **Null Hypothesis Significance Testing (NHST).**

Since Tea, we have developed [Tisane for generalized mixed-effects models](https://github.com/tea-lang-org/tisane) (for Python) and [rTisane for generalized models](https://github.com/tea-lang-org/rTisane) (for R). Both author statistical models from higher-level conceptual models. The latest DSL for supporting generalized mixed-effects models that combines insights from both Tisane and rTisane is [rTisanePy](https://github.com/tea-lang-org/rTisanePy) (for Python). Tea and the lessons we learned from developing and using it informed all of the above!

## How can I use Tea?
<a href='https://pypi.org/project/tealang/'>Tea is available on pip!</a>
```
pip install tealang
```

See community examples <a href='https://github.com/tea-lang-org/tea-lang/tree/master/examples'>here</a>. If you have trouble using Tea with your use case, feel free to open an issue, and we'll try to help. 

Step through <a href='https://github.com/tea-lang-org/tea-lang/blob/master/documentation.md'>a more guided, thorough documentation and a worked example</a>. 

## How can I cite Tea?
For now, please cite: 
```  
article{JunEtAl2019:Tea,
  title={Tea: A High-level Language and Runtime System for Automating Statistical Analysis},
  author={Jun, Eunice and Daum, Maureen and Roesch, Jared and Chasins, Sarah E. and Berger, Emery D. and Just, Rene and Reinecke, Katharina},
  journal={Proceedings of the 32nd Annual ACM Symposium on User Interface Software and Technology (UIST)},
  year={2019}
}
```

## How reliable is Tea?
Our constraint solver is based on
statistical texts (see <a href='http://tea-lang.org/index_files/tea_UIST2019.pdf'>our paper</a> for more info). 

If you find any bugs, please create a Github issue or let us know (email Eunice at emjun [at] cs.ucla.edu)!

## Where can I learn more about Tea?
Please find more information at <a href='https://tea-lang.org'>our website</a>. Tea is a research prototype we have been trying our best to maintain and improve since 2019. 

## I want to collaborate! Where do I begin?
This is great! We're excited to have new collaborators. :) 

To contribute *code*, please see <a href='./CONTRIBUTING.md'> docs and gudielines</a> and open an issue or pull request. 

If you want to use Tea for a project, talk about Tea's design, or anything else, please get in touch: emjun [at] cs.ucla.edu!

## I have ideas. I want to chat. 
Please reach out! We are nice :) Email Eunice at emjun [at] cs.ucla.edu!

## FAQs
### By the way, why Python?
Python is a common language for data science. We hope Tea can easily integrate
into user workflows. 

### What format should my data be in?
Tea accepts data either as a CSV or a Pandas DataFrame. Tea asumes data is in <a href='http://www.cookbook-r.com/Manipulating_data/Converting_data_between_wide_and_long_format/'>"long format."</a> 
