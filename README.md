# Verification Condition Generator

PyVCG is a utility library to generate VCs directly for
[CVC5](https://cvc5.github.io) or standard-compliant
[SMTLIB2](http://smtlib.cs.uiowa.edu/). The interface is deliberately
generic and it should be easy to add API support for other solvers in
the future.

This is pretty limited for now as the initial target is the expression
language of [TRLC](https://github.com/bmw-software-engineering/trlc).

## Features

This library provides a wrapper around SMTLIB with some additional
features:

* SMTLIB Scripts
* Automatic (minimal) logic discovery
* Basic sorts: Bool,
  [Int](https://smtlib.cs.uiowa.edu/theories-Ints.shtml),
  [Real](https://smtlib.cs.uiowa.edu/theories-Reals.shtml), and
  [String](https://cvc5.github.io/docs-ci/docs-main/theories/strings.html)
* Parametric sorts:
  [Sequences](https://cvc5.github.io/docs-ci/docs-main/theories/sequences.html)
* Datatype sorts: Enumerations and Records
* Uninterpreted functions
* Quantifiers
* Boolean expressions: not, and, or, xor, implication
* If-then-else expressions
* Comparisons: =, <, >, <=, >=
* Int -> Real conversion
* Real -> Int conversion (smtlib rounding (round-to-negative) and
  arithmetic rounding (round-nearest-away))
* Unary arithmetic: -, abs
* Binary Int arithmetic: +, -, *, smtlib div, smtlib mod, python div,
  ada remainder
* Binary Real arithmetic: +, -, *, /
* String operations: length, contains, prefix, suffix, concatenation
* Sequence operations: length, contains, access, concatenation
* Record operations: access

In addition this library provides a graph to build VCs with multiple
paths; and generating VCs for all paths. FastWP and higher-level
modelling for language features (e.g. ite, loops) are planned later.

## Drivers

Current support for outputs:

* SMTLIB (for writing and debugging)
* CVC5 API (for solving)

## Dependencies

### Run-time

* Python >= 3.9
* [cvc5](https://pypi.org/project/cvc5)

### Development

* [GNU Make](https://www.gnu.org/software/make)
* [coverage](https://pypi.org/project/coverage)
* [pycodestyle](https://pypi.org/project/pycodestyle)
* [pylint](https://pypi.org/project/pylint)

## Copyright & License

The sole copyright holder is Florian Schanda.

This library is licensed under the [GNU GPL version 3](LICENSE) (or
later).
