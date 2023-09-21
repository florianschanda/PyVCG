# PyVCG Release Notes

## Supported tools / standards

* SMTLIB 2.6 with string and sequence extensions
* CVC5

## Changelog


### 1.0.6-dev

* Add new driver for CVC5 (via SMTLIB files instead of the API).

### 1.0.5

* Fix python_requires, the expression acidentally excluded Python
  3.11. We should now correctly support it.

### 1.0.4

* Move to CVC 1.0.8. This means we can now support Python 3.11 as
  well.

### 1.0.3

* Pin to CVC5 1.0.5, as 1.0.7 is completely broken

### 1.0.2

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
