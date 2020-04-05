## FILES

## How do I use Tea?
Make sure that you have Python 3.7, pip (for Python 3.7), and pipenv (for Python 3.7) installed. 
Start a pipenv: `pipenv shell`
From inside your environment, download all dependencies from Pipfile (`pipenv update`). This will take awhile because it builds Z3.
Add Tea to your Python path by creating `.env` file that has the following one-liner in it: `PYTHONPATH=${PYTHONPATH}:${PWD}`
To run tests and see output, run: `pytest tests/test_integration.py -s`

The main code base is written in Python and lives in the `tea` directory. The `tests` directory is used for developing and debugging and uses datasets in the `datasets` directory. Not all the datasets used in `tests/test_tea.py` are included in the `datasets` repository. 
`tea/solver.py` contains the constraint solving module for both tests -> properties and properties -> tests.
`tea/ast.py` implements Tea's Abstract Syntax Tree (AST). 
`tea/build.py` builds up Tea's AST for programs.
`tea/dataset.py` contains a runtime data structure that represents and contains the data the user provides. 
`tea/evaluate.py` is the main interpreter file.
`tea/evaluate_helper_methods.py` contains the helper methods for `evaluate.py`.
`tea/evaluate_data_structures.py` contains the data structuers used in `evaluate.py` and `evaluate_helper_methods.py`.
`tea/errors.py` is empty. It will contain some code for providing helpful error messages.

## Can I use external datasets to create additional tests, documentation, and examples?
Yes! Try and use Tea with real data, that's what we hope for. :) If you do decide to include external datasets in Tea tests, documentation, and examples, please make sure to attribute credit to the sources in your files and add them to the list in [`SOURCES.md`](./SOURCES.MD).

**All of the above are still changing!**