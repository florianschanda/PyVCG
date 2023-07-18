# PyVCG Release Notes

## Supported tools / standards

* SMTLIB 2.6 with string and sequence extensions
* CVC5

## Changelog

### 1.0.2-dev

* Fix bug in printing smtlib string literals. They are now correctly
  escaped for both quotations and non-printable characters.

* Fix bug when printing smtlib comments with newlines.

### 1.0.1

* Fix bug where an uninterpreted function declaration did not
  contribute correctly to the logic selection.

* Adjust required Python version to 3.8 to 3.10 (as that is what CVC5
  currently supports).

### 1.0.0

* First release
