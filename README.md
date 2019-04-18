# tea-lang [![Build Status](https://travis-ci.com/emjun/tea-lang.svg?token=xtmHu9y9pvfxkHzbdxsu&branch=master)](https://travis-ci.com/emjun/tea-lang)

# [WIP] Tea: A High-level Language and Runtime System for Automating Statistical Analyses

## What is Tea?
Tea is a domain specific language for expressing the assertions and intentions/goals for statistical analyses (e.g., to compare two groups on an outcome). The user provides a dataset (currently only CSV) and a experimental design specification. The Tea runtime system then translates these high-level expressions, calculates properties about the data, and translates these properties into constarints to find a set of valid statistical tests. Tea uses Z3 as its constraint solver.

## How can I learn more about it?

We are preparing a manual and other documentation, but for now, the best overview and introduction is our technical paper: [https://arxiv.org/abs/1904.05387](https://arxiv.org/abs/1904.05387)!

## How do I use Tea?
Make sure that you have Python 3.7, pip (for Python 3.7), and pipenv (for Python 3.7) installed. 
Start a pipenv: `pipenv shell`
From inside your environment, download all dependencies from Pipfile (`pipenv update`). This will take awhile because it builds Z3.
Add Tea to your Python path by creating `.env` file that has the following one-liner in it: `PYTHONPATH=${PYTHONPATH}:${PWD}`
To run tests and see output, run: `pytest tests/integration_tests/test_integration.py -s`

The main code base is written in Python and lives in the `tea` directory. The `tests` directory is used for developing and debugging and uses datasets in the `datasets` directory. Not all the datasets used in `tests/test_tea.py` are included in the `datasets` repository. 
`tea/solver.py` contains the constraint solving module for both tests -> properties and properties -> tests.
`tea/ast.py` implements Tea's Abstract Syntax Tree (AST). 
`tea/build.py` builds up Tea's AST for programs.
`tea/dataset.py` contains a runtime data structure that represents and contains the data the user provides. 
`tea/evaluate.py` is the main interpreter file.
`tea/evaluate_helper_methods.py` contains the helper methods for `evaluate.py`.
`tea/evaluate_data_structures.py` contains the data structuers used in `evaluate.py` and `evaluate_helper_methods.py`.
`tea/errors.py` is empty. It will contain some code for providing helpful error messages.

**All of the above are still changing!**

## Why Python?
Many comparable data science tools are implemented as Python. People seem to like and use Python a lot for data stuff!

## How can I contribute?
You want to contribute? That's so great! Thank you so much!

It would be best to create a separate branch that we can merge when Tea is slightly more stable. :)
