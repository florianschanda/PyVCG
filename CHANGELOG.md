# PyVCG Release Notes

## Supported tools / standards

* SMTLIB 2.6 with string and sequence extensions
* CVC5

## Changelog


### 1.0.13-dev



### 1.0.12

* Move to CVC5 1.3.4

### 1.0.10

* Add support for "optional" types. These are really just datatypes
  with a single null constructor and a value constructor. However they
  come out correctly in Python as `null` or the actual value.

* Move to CVC5 1.3.2

### 1.0.9

* Reject recursive trees. Thank you to Melody Ma for uncovering
  it. The API now raises an exception `Recursion` if you attempt to
  construct an AST that is not a DAG. (Note: you can of course still
  re-use nodes, as long as there are no loop in the DAG.)

* Add support for self-recursive records. This is a pre-cursor to full
  mutual recursion, but it is enough for TRLC.

  * The `add_component` method of `Record` can take the record sort
    itself.

  * A new expression `Record_Null_Check` can be used to check if a
    given term is equal to the null constructor. This can only be used
    on recursive records. Note that if you have a recursive record,
    then this is a pre-condition that you need to check on any access;
    otherwise you might get unexpected results (it is perfectly
    possible to access a record null constructor, you just get an
    uninterpreted function result). This checking has to happen inside
    the program driving PyVCG, it cannot happen inside PyVCG.

* Move to CVC5 1.3.1.

* Add support for Python up to 3.14.

### 1.0.8

* Move to CVC5 1.3.0. This should now include Python support up to
  3.13.

### 1.0.7

* Move to CVC5 1.2.0. This should now include Windows support.

### 1.0.6

* Add new driver for CVC5 (via SMTLIB files instead of the API).

### 1.0.5

* Fix python_requires, the expression acidentally excluded Python
  3.11. We should now correctly support it.

### 1.0.4

* Move to CVC5 1.0.8. This means we can now support Python 3.11 as
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
