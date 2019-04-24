# tea-lang [![Build Status](https://travis-ci.com/emjun/tea-lang.svg?branch=master)](https://travis-ci.com/emjun/tea-lang)

# [WIP] Tea: A High-level Language and Runtime System for Automating Statistical Analyses

## What is Tea?
Tea is a domain specific programming language that automates statistical test
selection and execution. Tea is currently written in/for Python. 

Tea has an <a href='https://arxiv.org/pdf/1904.05387.pdf'>academic Arxiv paper</a>. 

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
Tea currently provides a module to conduct Null Hypothesis Significance
Testing (NHST). 

*We are actively working on expanding the kinds of analyses Tea can support. Some ideas we have: Bayesian inference and linear modeling.*

## How can I use Tea?
Tea will **very soon** be available on pip! Check back for updates :)

## How can I cite Tea?
For now, please cite it!: 
```  
article{JunEtAl2019:Tea,
  title={Tea: A High-level Language and Runtime System for Automating Statistical Analysis},
  author={Jun, Eunice and Daum, Maureen and Roesch, Jared and Chasins, Sarah E. and Berger, Emery D. and Just, Rene and Reinecke, Katharina},
  journal={Arxiv},
  year={2019}
}
```

## How reliable is Tea?
Tea is currently a research prototype. Our constraint solver is based on
statistical texts (see <a href='https://arxiv.org/pdf/1904.05387.pdf'>our paper</a> for more info). 

If you find any bugs, please let us know (email Eunice at emjun [at] cs.washington.edu)!

## I want to collaborate! Where do I begin?
This is great! We're excited to have new collaborators. :) 

To contribute *code*, please see <a href='./CONTRIBUTING.md'> docs and
gudielines</a> and open an issue or pull request. 

If you want to use Tea for a
project, talk about Tea's design, or anything else, please get in touch: emjun at
cs.washington.edu.

## Where can I learn more about Tea?
Please find more information at <a href='https://www.tea-lang.org'>our website</a>. 

## I have ideas. I want to chat. 
Please reach out! We are nice :): emjun at cs.washington.edu


### By the way, why Python?
Python is a common language for data science. We hope Tea can easily integrate
into user workflows. 

*We are working on compiling Tea programs to different target languages, including R.*