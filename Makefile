precommit: style lint test
	@echo "\033[33mprecommit:\033[0m \033[32macceptable\033[0m"

test:
	@echo "\033[33mprecommit:\033[0m unit tests"
	@coverage run \
		--branch --rcfile=coverage.cfg \
		-m unittest discover -s tests -v
	@coverage html --rcfile=coverage.cfg
	@coverage report --rcfile=coverage.cfg --fail-under=100

style:
	@echo "\033[33mprecommit:\033[0m style check"
	@python3 -m pycodestyle pyvcg tests

lint: style
	@echo "\033[33mprecommit:\033[0m lint check"
	@python3 -m pylint --rcfile=pylint3.cfg pyvcg \
		--reports=no \
		--score=no \
		--extension-pkg-allow-list=cvc5

package:
	@git clean -xdf
	@python3 setup.py sdist bdist_wheel

release:
	make precommit
	python3 -m util.release
	git push
	python3 -m util.github_release
	make package
	python3 -m twine upload --repository pypi dist/*
	python3 -m util.bump_version_post_release
	git push
