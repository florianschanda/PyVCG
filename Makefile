test:
	coverage run --branch --rcfile=coverage.cfg -m unittest discover -s tests -v
	coverage html --rcfile=coverage.cfg
	coverage report --rcfile=coverage.cfg
