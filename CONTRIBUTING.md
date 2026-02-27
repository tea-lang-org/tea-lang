## How do I use Tea?

Make sure that you have Python 3.10+ and [Poetry](https://python-poetry.org/) installed.

Install all dependencies:
```
poetry install
```

To run all tests:
```
poetry run pytest tests/ -v
```

To run tests with coverage:
```
poetry run pytest --cov=tea tests/
```

## Project Structure

The main code base lives in the `tea` directory. The `tests` directory contains
test suites using datasets stored locally in `tests/data/` (see
`tests/data/README.md` for dataset sources and attribution).

- `tea/api.py` — User-facing API functions (`data`, `define_variables`, `hypothesize`, etc.)
- `tea/ast.py` — Tea's Abstract Syntax Tree (AST) definitions
- `tea/build.py` — Builds Tea's AST for programs
- `tea/z3_solver/solver.py` — Constraint solving module (tests &harr; properties)
- `tea/runtimeDataStructures/dataset.py` — Runtime data structure for user-provided data
- `tea/helpers/evaluateHelperMethods.py` — Statistical test execution helpers
- `tea/vardata_factory.py` — Factory for creating VarData from AST nodes

## Can I use external datasets to create additional tests, documentation, and examples?

Yes! Try and use Tea with real data, that's what we hope for. If you do decide
to include external datasets in Tea tests, documentation, and examples, please
make sure to attribute credit to the sources in your files and add them to the
list in [`SOURCES.md`](./SOURCES.md) and `tests/data/README.md`.
