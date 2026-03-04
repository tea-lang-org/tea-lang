init:
	pip install poetry
	poetry install

test:
	poetry run pytest --cov=tea ./tests/
