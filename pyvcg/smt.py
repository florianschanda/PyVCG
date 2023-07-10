#!/usr/bin/env python3
##############################################################################
##                                                                          ##
##                   Verification Condition Generator                       ##
##                                                                          ##
##              Copyright (C) 2023, Florian Schanda                         ##
##                                                                          ##
##  This file is part of PyVCG.                                             ##
##                                                                          ##
##  PyVCG is free software: you can redistribute it and/or modify it        ##
##  under the terms of the GNU General Public License as published by       ##
##  the Free Software Foundation, either version 3 of the License, or       ##
##  (at your option) any later version.                                     ##
##                                                                          ##
##  PyVCG is distributed in the hope that it will be useful, but            ##
##  WITHOUT ANY WARRANTY; without even the implied warranty of              ##
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU        ##
##  General Public License for more details.                                ##
##                                                                          ##
##  You should have received a copy of the GNU General Public License       ##
##  along with PyVCG. If not, see <http://www.gnu.org/licenses/>.           ##
##                                                                          ##
##############################################################################

from abc import ABCMeta, abstractmethod
from fractions import Fraction


##############################################################################
# Abstract Visitors
##############################################################################

class Visitor(metaclass=ABCMeta):
    @abstractmethod
    def visit_script(self, node, logic, functions):
        assert isinstance(node, Script)
        assert isinstance(logic, str)
        assert isinstance(functions, set)
        assert all(isinstance(function, str)
                   for function in functions)

    @abstractmethod
    def visit_constant_declaration(self, node, tr_symbol, tr_value):
        assert isinstance(node, Constant_Declaration)

    @abstractmethod
    def visit_function_declaration(self, node, tr_sort, tr_body):
        assert isinstance(node, Function_Declaration)

    @abstractmethod
    def visit_assertion(self, node, tr_expression):
        assert isinstance(node, Assertion)

    @abstractmethod
    def visit_enumeration_declaration(self, node):
        assert isinstance(node, Enumeration_Declaration)

    @abstractmethod
    def visit_record_declaration(self, node):
        assert isinstance(node, Record_Declaration)

    @abstractmethod
    def visit_sort(self, node):
        assert isinstance(node, Sort)

    @abstractmethod
    def visit_parametric_sort(self, node, tr_parameters):
        assert isinstance(node, Parametric_Sort)
        assert isinstance(tr_parameters, list)

    @abstractmethod
    def visit_function(self, node):
        assert isinstance(node, Function)

    @abstractmethod
    def visit_enumeration(self, node):
        assert isinstance(node, Enumeration)

    @abstractmethod
    def visit_record(self, node):
        assert isinstance(node, Record)

    @abstractmethod
    def visit_boolean_literal(self, node, tr_sort):
        assert isinstance(node, Boolean_Literal)

    @abstractmethod
    def visit_integer_literal(self, node, tr_sort):
        assert isinstance(node, Integer_Literal)

    @abstractmethod
    def visit_real_literal(self, node, tr_sort):
        assert isinstance(node, Real_Literal)

    @abstractmethod
    def visit_enumeration_literal(self, node, tr_sort):
        assert isinstance(node, Enumeration_Literal)

    @abstractmethod
    def visit_string_literal(self, node, tr_sort):
        assert isinstance(node, String_Literal)

    @abstractmethod
    def visit_constant(self, node, tr_sort):
        assert isinstance(node, Constant)

    @abstractmethod
    def visit_bound_variable(self, node, tr_sort):
        assert isinstance(node, Bound_Variable)

    @abstractmethod
    def visit_boolean_negation(self, node, tr_sort, tr_expression):
        assert isinstance(node, Boolean_Negation)

    @abstractmethod
    def visit_conjunction(self, node, tr_sort, tr_terms):
        assert isinstance(node, Conjunction)
        assert isinstance(tr_terms, list)

    @abstractmethod
    def visit_disjunction(self, node, tr_sort, tr_terms):
        assert isinstance(node, Disjunction)
        assert isinstance(tr_terms, list)

    @abstractmethod
    def visit_exclusive_disjunction(self, node, tr_sort, tr_lhs, tr_rhs):
        assert isinstance(node, Exclusive_Disjunction)

    @abstractmethod
    def visit_implication(self, node, tr_sort, tr_lhs, tr_rhs):
        assert isinstance(node, Implication)

    @abstractmethod
    def visit_comparison(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Comparison)

    @abstractmethod
    def visit_conversion_to_real(self, node, tr_value):
        assert isinstance(node, Conversion_To_Real)

    @abstractmethod
    def visit_conversion_to_integer(self, node, tr_value):
        assert isinstance(node, Conversion_To_Integer)

    @abstractmethod
    def visit_unary_int_arithmetic_op(self, node, tr_operand):
        assert isinstance(node, Unary_Int_Arithmetic_Op)

    @abstractmethod
    def visit_unary_real_arithmetic_op(self, node, tr_operand):
        assert isinstance(node, Unary_Real_Arithmetic_Op)

    @abstractmethod
    def visit_binary_int_arithmetic_op(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Binary_Int_Arithmetic_Op)

    @abstractmethod
    def visit_binary_real_arithmetic_op(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Binary_Real_Arithmetic_Op)

    @abstractmethod
    def visit_string_length(self, node, tr_string):
        assert isinstance(node, String_Length)

    @abstractmethod
    def visit_string_predicate(self, node, tr_first, tr_second):
        assert isinstance(node, String_Predicate)

    @abstractmethod
    def visit_string_concatenation(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, String_Concatenation)

    @abstractmethod
    def visit_sequence_length(self, node, tr_sequence):
        assert isinstance(node, Sequence_Length)

    @abstractmethod
    def visit_sequence_index(self, node, tr_sequence, tr_index):
        assert isinstance(node, Sequence_Index)

    @abstractmethod
    def visit_sequence_contains(self, node, tr_sequence, tr_item):
        assert isinstance(node, Sequence_Contains)

    @abstractmethod
    def visit_sequence_concatenation(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Sequence_Concatenation)

    @abstractmethod
    def visit_record_access(self, node, tr_record):
        assert isinstance(node, Record_Access)

    @abstractmethod
    def visit_function_application(self, node, tr_function, tr_args):
        assert isinstance(node, Function_Application)
        assert isinstance(tr_args, list)

    @abstractmethod
    def visit_conditional(self, node, tr_condition, tr_true, tr_false):
        assert isinstance(node, Conditional)

    @abstractmethod
    def visit_quantifier(self, node, tr_variables, tr_body):
        assert isinstance(node, Quantifier)


class VC_Writer(Visitor, metaclass=ABCMeta):
    pass


class VC_Solver(Visitor, metaclass=ABCMeta):
    @abstractmethod
    def solve(self):
        pass

    @abstractmethod
    def get_status(self):
        pass

    @abstractmethod
    def get_values(self):
        pass


##############################################################################
# Concrete Visitors
##############################################################################

class Logic_Visitor(Visitor):
    def __init__(self):
        self.logics    = set()
        self.functions = set()

    def get_logic_string(self):
        allowed_logics = set(["quant", "int", "real",
                              "strings", "arrays", "sequences",
                              "nonlinear", "datatypes",
                              "functions"])

        assert not self.logics or self.logics < allowed_logics, \
            "%s is not a permitted logic" % (self.logics - allowed_logics)

        if "quant" in self.logics:
            logic = ""
        else:
            logic = "QF_"

        if "arrays" in self.logics:  # pragma: no cover
            logic += "A"

        if "functions" in self.logics or self.functions:
            logic += "UF"

        if "datatypes" in self.logics:
            logic += "DT"

        if "strings" in self.logics or "sequences" in self.logics:
            logic += "S"

        if "int" in self.logics or \
           "real" in self.logics:
            if "nonlinear" in self.logics:  # pragma: no cover
                logic += "N"
            else:
                logic += "L"
            if "int" in self.logics:
                logic += "I"
            if "real" in self.logics:
                logic += "R"
            logic += "A"

        if logic == "":  # pragma: no cover
            return "SAT"
        elif logic == "QF_":
            return "QF_SAT"
        else:
            return logic

    def get_required_functions(self):
        return self.functions

    def visit_script(self, node, logic, functions):  # pragma: no cover
        assert False

    def visit_constant_declaration(self, node, tr_symbol, tr_value):
        assert isinstance(node, Constant_Declaration)

    def visit_function_declaration(self, node, tr_sort, tr_body):
        assert isinstance(node, Function_Declaration)
        self.logics.add("functions")

    def visit_assertion(self, node, tr_expression):
        assert isinstance(node, Assertion)

    def visit_enumeration_declaration(self, node):
        assert isinstance(node, Enumeration_Declaration)
        self.logics.add("datatypes")

    def visit_record_declaration(self, node):
        assert isinstance(node, Record_Declaration)
        self.logics.add("datatypes")
        node.sort.walk(self)

    def visit_sort(self, node):
        assert isinstance(node, Sort)
        if node.name == "Bool":
            pass
        elif node.name == "Int":
            self.logics.add("int")
        elif node.name == "Real":
            self.logics.add("real")
        elif node.name == "String":
            self.logics.add("strings")
        else:
            assert False, "unexpected base sort %s" % node.name

    def visit_parametric_sort(self, node, tr_parameters):
        assert isinstance(node, Parametric_Sort)
        assert isinstance(tr_parameters, list)

        if node.name == "Seq":
            self.logics.add("sequences")
        else:
            assert False, "unexpected base sort %s" % node.name

    def visit_function(self, node):
        assert isinstance(node, Function)
        self.logics.add("functions")

    def visit_enumeration(self, node):
        assert isinstance(node, Enumeration)
        self.logics.add("datatypes")

    def visit_record(self, node):
        assert isinstance(node, Record)
        self.logics.add("datatypes")
        for sort in node.components.values():
            sort.walk(self)

    def visit_boolean_literal(self, node, tr_sort):
        assert isinstance(node, Boolean_Literal)

    def visit_integer_literal(self, node, tr_sort):
        assert isinstance(node, Integer_Literal)

    def visit_real_literal(self, node, tr_sort):
        assert isinstance(node, Real_Literal)

    def visit_enumeration_literal(self, node, tr_sort):
        assert isinstance(node, Enumeration_Literal)
        self.logics.add("datatypes")

    def visit_string_literal(self, node, tr_sort):
        assert isinstance(node, String_Literal)
        self.logics.add("strings")

    def visit_constant(self, node, tr_sort):
        assert isinstance(node, Constant)

    def visit_bound_variable(self, node, tr_sort):
        assert isinstance(node, Bound_Variable)

    def visit_boolean_negation(self, node, tr_sort, tr_expression):
        assert isinstance(node, Boolean_Negation)

    def visit_conjunction(self, node, tr_sort, tr_terms):
        assert isinstance(node, Conjunction)
        assert isinstance(tr_terms, list)

    def visit_disjunction(self, node, tr_sort, tr_terms):
        assert isinstance(node, Disjunction)
        assert isinstance(tr_terms, list)

    def visit_exclusive_disjunction(self, node, tr_sort, tr_lhs, tr_rhs):
        assert isinstance(node, Exclusive_Disjunction)

    def visit_implication(self, node, tr_sort, tr_lhs, tr_rhs):
        assert isinstance(node, Implication)

    def visit_comparison(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Comparison)

    def visit_conversion_to_real(self, node, tr_value):
        assert isinstance(node, Conversion_To_Real)

    def visit_conversion_to_integer(self, node, tr_value):
        assert isinstance(node, Conversion_To_Integer)
        if node.rounding == "rna":
            self.functions.add("to_int_rna")

    def visit_unary_int_arithmetic_op(self, node, tr_operand):
        assert isinstance(node, Unary_Int_Arithmetic_Op)

    def visit_unary_real_arithmetic_op(self, node, tr_operand):
        assert isinstance(node, Unary_Real_Arithmetic_Op)

    def visit_binary_int_arithmetic_op(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Binary_Int_Arithmetic_Op)
        linear = node.operator in ("+", "-") or \
            (node.operator == "*" and (node.lhs.is_static() or
                                       node.rhs.is_static())) or \
            (node.lhs.is_static() and node.rhs.is_static())
        if not linear:
            self.logics.add("nonlinear")
        if node.operator in ("floor_div", "ada_remainder"):
            self.functions.add(node.operator)

    def visit_binary_real_arithmetic_op(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Binary_Real_Arithmetic_Op)
        linear = node.operator in ("+", "-") or \
            (node.operator == "*" and (node.lhs.is_static() or
                                       node.rhs.is_static())) or \
            (node.lhs.is_static() and node.rhs.is_static())
        if not linear:
            self.logics.add("nonlinear")

    def visit_string_length(self, node, tr_string):
        assert isinstance(node, String_Length)
        self.logics.add("strings")

    def visit_string_predicate(self, node, tr_first, tr_second):
        assert isinstance(node, String_Predicate)
        self.logics.add("strings")

    def visit_string_concatenation(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, String_Concatenation)
        self.logics.add("strings")

    def visit_sequence_length(self, node, tr_sequence):
        assert isinstance(node, Sequence_Length)
        self.logics.add("sequences")

    def visit_sequence_index(self, node, tr_sequence, tr_index):
        assert isinstance(node, Sequence_Index)
        self.logics.add("sequences")

    def visit_sequence_contains(self, node, tr_sequence, tr_item):
        assert isinstance(node, Sequence_Contains)
        self.logics.add("sequences")

    def visit_sequence_concatenation(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Sequence_Concatenation)
        self.logics.add("sequences")

    def visit_record_access(self, node, tr_record):
        assert isinstance(node, Record_Access)
        self.logics.add("datatypes")

    def visit_function_application(self, node, tr_function, tr_args):
        assert isinstance(node, Function_Application)
        assert isinstance(tr_args, list)
        self.logics.add("functions")

    def visit_conditional(self, node, tr_condition, tr_true, tr_false):
        assert isinstance(node, Conditional)

    def visit_quantifier(self, node, tr_variables, tr_body):
        assert isinstance(node, Quantifier)
        self.logics.add("quant")


##############################################################################
# SMTLIB
##############################################################################

class Node(metaclass=ABCMeta):
    @abstractmethod
    def walk(self, visitor):
        assert isinstance(visitor, Visitor)


##############################################################################
# Top-level items
##############################################################################

class Script(Node):
    def __init__(self):
        self.statements      = []
        self.relevant_values = []
        self.logic           = Logic_Visitor()

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_script(self,
                                    self.logic.get_logic_string(),
                                    self.logic.get_required_functions())

    def add_statement(self, statement):
        assert isinstance(statement, Statement)
        self.statements.append(statement)
        statement.walk(self.logic)

        if isinstance(statement, Constant_Declaration) and \
           statement.is_relevant:
            self.relevant_values.append(statement.symbol)

    def generate_vc(self, visitor):
        assert isinstance(visitor, VC_Writer)
        return self.walk(visitor)

    def solve_vc(self, visitor):
        assert isinstance(visitor, VC_Solver)
        self.walk(visitor)
        visitor.solve()
        return visitor.get_status(), visitor.get_values()


class Statement(Node, metaclass=ABCMeta):
    def __init__(self, comment):
        assert isinstance(comment, str) or comment is None
        self.comment = comment


class Sort(Node):
    def __init__(self, name):
        assert isinstance(name, str) and "|" not in name

        self.name = name

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_sort(self)


class Parametric_Sort(Sort, metaclass=ABCMeta):
    def __init__(self, name, *parameters):
        super().__init__(name)
        assert all(isinstance(parameter, Sort) for parameter in parameters)

        self.parameters = parameters

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        tr_parameters = [parameter.walk(visitor)
                         for parameter in self.parameters]
        return visitor.visit_parametric_sort(self, tr_parameters)


BUILTIN_BOOLEAN = Sort("Bool")
BUILTIN_INTEGER = Sort("Int")
BUILTIN_REAL    = Sort("Real")
BUILTIN_STRING  = Sort("String")


class Expression(Node, metaclass=ABCMeta):
    def __init__(self, sort):
        assert isinstance(sort, Sort)

        self.sort = sort

    def is_static(self):
        return False

    def is_static_true(self):
        return False

    def is_static_false(self):
        return False


class Function(Node):
    def __init__(self, name, sort, *parameters):
        assert isinstance(name, str) and "|" not in name
        assert isinstance(sort, Sort)
        assert isinstance(parameters, tuple)
        assert all(isinstance(param, Bound_Variable) for param in parameters)
        self.name       = name
        self.sort       = sort
        self.parameters = parameters
        self.body       = None

    def define_body(self, expression):
        assert isinstance(expression, Expression)
        assert expression.sort is self.sort
        self.body = expression

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_function(self)


##############################################################################
# Statements
##############################################################################

class Constant_Declaration(Statement):
    def __init__(self, symbol, value=None, comment=None, relevant=False):
        super().__init__(comment)
        assert isinstance(symbol, Constant)
        assert value is None or (isinstance(value, Expression) and
                                 value.sort is symbol.sort)
        assert isinstance(relevant, bool)

        self.symbol      = symbol
        self.value       = value
        self.is_relevant = relevant

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        tr_symbol = self.symbol.walk(visitor)
        if self.value is None:
            tr_value = None
        else:
            tr_value = self.value.walk(visitor)
        return visitor.visit_constant_declaration(self, tr_symbol, tr_value)


class Function_Declaration(Statement):
    def __init__(self, function, comment=None):
        super().__init__(comment)
        assert isinstance(function, Function)
        self.function = function

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        tr_sort     = self.function.sort.walk(visitor)
        if self.function.body is None:
            tr_body = None
        else:
            tr_body = self.function.body.walk(visitor)
        return visitor.visit_function_declaration(self,
                                                  tr_sort,
                                                  tr_body)


class Assertion(Statement):
    def __init__(self, expression, comment=None):
        super().__init__(comment)
        assert isinstance(expression, Expression)
        assert expression.sort is BUILTIN_BOOLEAN

        self.expression = expression

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_assertion(self, self.expression.walk(visitor))


class Enumeration_Declaration(Statement):
    def __init__(self, sort, comment=None):
        super().__init__(comment)
        assert isinstance(sort, Enumeration)
        self.sort = sort

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_enumeration_declaration(self)


class Record_Declaration(Statement):
    def __init__(self, sort, comment=None):
        super().__init__(comment)
        assert isinstance(sort, Record)
        self.sort = sort

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_record_declaration(self)


##############################################################################
# Sorts
##############################################################################

class Enumeration(Sort):
    def __init__(self, name):
        super().__init__(name)
        self.literals = []

    def add_literal(self, name):
        assert isinstance(name, str)
        assert name not in self.literals

        self.literals.append(name)

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_enumeration(self)


class Record(Sort):
    def __init__(self, name):
        super().__init__(name)
        self.components  = {}

    def add_component(self, name, sort):
        assert isinstance(name, str)
        assert isinstance(sort, Sort)
        assert name not in self.components

        self.components[name] = sort

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_record(self)


class Sequence_Sort(Parametric_Sort):
    def __init__(self, element_sort):
        assert isinstance(element_sort, Sort)
        super().__init__("Seq", element_sort)

    def element_sort(self):
        return self.parameters[0]


##############################################################################
# Expressions
##############################################################################

##############################################################################
# Literals and constants
##############################################################################

class Literal(Expression, metaclass=ABCMeta):
    def is_static(self):
        return True


class Boolean_Literal(Literal):
    def __init__(self, value):
        super().__init__(BUILTIN_BOOLEAN)
        assert isinstance(value, bool)

        self.value = value

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_boolean_literal(self, self.sort.walk(visitor))

    def is_static_true(self):
        return self.value

    def is_static_false(self):
        return not self.value


class Integer_Literal(Literal):
    def __init__(self, value):
        super().__init__(BUILTIN_INTEGER)
        assert isinstance(value, int)

        self.value = value

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_integer_literal(self, self.sort.walk(visitor))


class Real_Literal(Literal):
    def __init__(self, value):
        super().__init__(BUILTIN_REAL)
        assert isinstance(value, (int, Fraction))

        if isinstance(value, int):
            self.value = Fraction(value)
        else:
            self.value = value

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_real_literal(self, self.sort.walk(visitor))


class Enumeration_Literal(Literal):
    def __init__(self, enumeration, value):
        assert isinstance(enumeration, Enumeration)
        assert value in enumeration.literals
        super().__init__(enumeration)
        self.value = value

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_enumeration_literal(self, self.sort.walk(visitor))


class String_Literal(Literal):
    def __init__(self, value):
        assert isinstance(value, str)
        super().__init__(BUILTIN_STRING)
        self.value = value

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_string_literal(self, self.sort.walk(visitor))


class Constant(Expression):
    def __init__(self, sort, name):
        super().__init__(sort)
        assert isinstance(name, str) and "|" not in name
        self.name = name

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_constant(self, self.sort.walk(visitor))


class Bound_Variable(Expression):
    def __init__(self, sort, name):
        super().__init__(sort)
        assert isinstance(name, str) and "|" not in name
        self.name = name

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_bound_variable(self, self.sort.walk(visitor))


##############################################################################
# Boolean terms
##############################################################################

class Boolean_Negation(Expression):
    def __init__(self, expression):
        assert isinstance(expression, Expression)
        super().__init__(expression.sort)

        self.expression = expression

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_boolean_negation(self,
                                              self.sort.walk(visitor),
                                              self.expression.walk(visitor))


class Conjunction(Expression):
    def __init__(self, *terms):
        assert isinstance(terms, tuple)
        assert len(terms) >= 2
        assert all(isinstance(term, Expression) and
                   term.sort is BUILTIN_BOOLEAN
                   for term in terms)
        super().__init__(BUILTIN_BOOLEAN)

        self.terms = terms

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        tr_terms = [term.walk(visitor) for term in self.terms]
        return visitor.visit_conjunction(self,
                                         self.sort.walk(visitor),
                                         tr_terms)


class Disjunction(Expression):
    def __init__(self, *terms):
        assert isinstance(terms, tuple)
        assert len(terms) >= 2
        assert all(isinstance(term, Expression) and
                   term.sort is BUILTIN_BOOLEAN
                   for term in terms)
        super().__init__(BUILTIN_BOOLEAN)

        self.terms = terms

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        tr_terms = [term.walk(visitor) for term in self.terms]
        return visitor.visit_disjunction(self,
                                         self.sort.walk(visitor),
                                         tr_terms)


class Exclusive_Disjunction(Expression):
    def __init__(self, lhs, rhs):
        assert isinstance(lhs, Expression) and lhs.sort is BUILTIN_BOOLEAN
        assert isinstance(rhs, Expression) and rhs.sort is BUILTIN_BOOLEAN
        super().__init__(BUILTIN_BOOLEAN)

        self.lhs = lhs
        self.rhs = rhs

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_exclusive_disjunction(self,
                                                   self.sort.walk(visitor),
                                                   self.lhs.walk(visitor),
                                                   self.rhs.walk(visitor))


class Implication(Expression):
    def __init__(self, lhs, rhs):
        assert isinstance(lhs, Expression) and lhs.sort is BUILTIN_BOOLEAN
        assert isinstance(rhs, Expression) and rhs.sort is BUILTIN_BOOLEAN
        super().__init__(BUILTIN_BOOLEAN)

        self.lhs = lhs
        self.rhs = rhs

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_implication(self,
                                         self.sort.walk(visitor),
                                         self.lhs.walk(visitor),
                                         self.rhs.walk(visitor))


##############################################################################
# Comparisons
##############################################################################

class Comparison(Expression):
    def __init__(self, operator, lhs, rhs):
        assert operator in ("<", ">", "<=", ">=", "=")
        assert isinstance(lhs, Expression)
        assert isinstance(rhs, Expression)
        assert lhs.sort is rhs.sort
        super().__init__(BUILTIN_BOOLEAN)

        self.operator = operator
        self.lhs      = lhs
        self.rhs      = rhs

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        tr_lhs = self.lhs.walk(visitor)
        tr_rhs = self.rhs.walk(visitor)
        return visitor.visit_comparison(self, tr_lhs, tr_rhs)


##############################################################################
# Arithmetic & Functions
##############################################################################

class Conversion_To_Real(Expression):
    def __init__(self, value):
        assert isinstance(value, Expression)
        assert value.sort is BUILTIN_INTEGER
        super().__init__(BUILTIN_REAL)
        self.value = value

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_conversion_to_real(self,
                                                self.value.walk(visitor))


class Conversion_To_Integer(Expression):
    def __init__(self, rounding, value):
        assert rounding in ("rtn", "rna")
        assert isinstance(value, Expression)
        assert value.sort is BUILTIN_REAL
        super().__init__(BUILTIN_INTEGER)
        self.rounding = rounding
        self.value    = value

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_conversion_to_integer(self,
                                                   self.value.walk(visitor))


class Unary_Int_Arithmetic_Op(Expression):
    def __init__(self, operator, operand):
        assert operator in ("-", "abs")
        assert isinstance(operand, Expression)
        assert operand.sort is BUILTIN_INTEGER
        super().__init__(operand.sort)

        self.operator = operator
        self.operand  = operand

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        tr_operand = self.operand.walk(visitor)
        return visitor.visit_unary_int_arithmetic_op(self, tr_operand)


class Unary_Real_Arithmetic_Op(Expression):
    def __init__(self, operator, operand):
        assert operator in ("-", "abs")
        assert isinstance(operand, Expression)
        assert operand.sort is BUILTIN_REAL
        super().__init__(operand.sort)

        self.operator = operator
        self.operand  = operand

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        tr_operand = self.operand.walk(visitor)
        return visitor.visit_unary_real_arithmetic_op(self, tr_operand)


class Binary_Int_Arithmetic_Op(Expression):
    def __init__(self, operator, lhs, rhs):
        assert operator in ("+", "-", "*", "div", "mod",
                            "floor_div", "ada_remainder")
        assert isinstance(lhs, Expression)
        assert isinstance(rhs, Expression)
        assert lhs.sort.name == "Int"
        assert lhs.sort is rhs.sort
        super().__init__(lhs.sort)

        self.operator = operator
        self.lhs      = lhs
        self.rhs      = rhs

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        tr_lhs = self.lhs.walk(visitor)
        tr_rhs = self.rhs.walk(visitor)
        return visitor.visit_binary_int_arithmetic_op(self, tr_lhs, tr_rhs)


class Binary_Real_Arithmetic_Op(Expression):
    def __init__(self, operator, lhs, rhs):
        assert operator in ("+", "-", "*", "/")
        assert isinstance(lhs, Expression)
        assert isinstance(rhs, Expression)
        assert lhs.sort.name == "Real"
        assert lhs.sort is rhs.sort
        super().__init__(lhs.sort)

        self.operator = operator
        self.lhs      = lhs
        self.rhs      = rhs

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        tr_lhs = self.lhs.walk(visitor)
        tr_rhs = self.rhs.walk(visitor)
        return visitor.visit_binary_real_arithmetic_op(self, tr_lhs, tr_rhs)


class String_Length(Expression):
    def __init__(self, string):
        assert isinstance(string, Expression)
        assert string.sort is BUILTIN_STRING
        super().__init__(BUILTIN_INTEGER)
        self.string = string

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_string_length(self, self.string.walk(visitor))


class String_Predicate(Expression):
    def __init__(self, operation, first, second):
        assert operation in ("contains", "prefixof", "suffixof")
        assert isinstance(first, Expression)
        assert first.sort is BUILTIN_STRING
        assert isinstance(second, Expression)
        assert second.sort is BUILTIN_STRING
        super().__init__(BUILTIN_BOOLEAN)
        self.operation = operation
        self.first     = first
        self.second    = second

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_string_predicate(self,
                                              self.first.walk(visitor),
                                              self.second.walk(visitor))


class String_Concatenation(Expression):
    def __init__(self, lhs, rhs):
        assert isinstance(lhs, Expression)
        assert lhs.sort is BUILTIN_STRING
        assert isinstance(rhs, Expression)
        assert rhs.sort is BUILTIN_STRING
        super().__init__(BUILTIN_STRING)
        self.lhs = lhs
        self.rhs = rhs

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_string_concatenation(self,
                                                  self.lhs.walk(visitor),
                                                  self.rhs.walk(visitor))


class Sequence_Length(Expression):
    def __init__(self, sequence):
        assert isinstance(sequence, Expression)
        assert isinstance(sequence.sort, Sequence_Sort)
        super().__init__(BUILTIN_INTEGER)
        self.sequence = sequence

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_sequence_length(self,
                                             self.sequence.walk(visitor))


class Sequence_Index(Expression):
    def __init__(self, sequence, index):
        assert isinstance(sequence, Expression)
        assert isinstance(sequence.sort, Sequence_Sort)
        assert isinstance(index, Expression)
        assert index.sort is BUILTIN_INTEGER
        super().__init__(sequence.sort.element_sort())
        self.sequence = sequence
        self.index    = index

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_sequence_index(self,
                                            self.sequence.walk(visitor),
                                            self.index.walk(visitor))


class Sequence_Contains(Expression):
    def __init__(self, sequence, item):
        assert isinstance(sequence, Expression)
        assert isinstance(sequence.sort, Sequence_Sort)
        assert isinstance(item, Expression)
        assert sequence.sort.element_sort() is item.sort
        super().__init__(BUILTIN_BOOLEAN)
        self.sequence = sequence
        self.item     = item

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_sequence_contains(self,
                                               self.sequence.walk(visitor),
                                               self.item.walk(visitor))


class Sequence_Concatenation(Expression):
    def __init__(self, lhs, rhs):
        assert isinstance(lhs, Expression)
        assert isinstance(lhs.sort, Sequence_Sort)
        assert isinstance(rhs, Expression)
        assert lhs.sort is rhs.sort
        super().__init__(lhs.sort)
        self.lhs = lhs
        self.rhs = rhs

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_sequence_concatenation(self,
                                                    self.lhs.walk(visitor),
                                                    self.rhs.walk(visitor))


class Record_Access(Expression):
    def __init__(self, record, component):
        assert isinstance(record, Expression)
        assert isinstance(record.sort, Record)
        assert isinstance(component, str)
        assert component in record.sort.components
        super().__init__(record.sort.components[component])
        self.record    = record
        self.component = component

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_record_access(self,
                                           self.record.walk(visitor))


class Function_Application(Expression):
    def __init__(self, function, *arguments):
        assert isinstance(function, Function)
        assert isinstance(arguments, tuple)
        assert len(arguments) == len(function.parameters)
        assert all(isinstance(arg, Expression) for arg in arguments)
        assert all(arg.sort is par.sort
                   for arg, par in zip(arguments, function.parameters))
        super().__init__(function.sort)
        self.function  = function
        self.arguments = arguments

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_function_application(
            self,
            self.function.walk(visitor),
            [arg.walk(visitor) for arg in self.arguments])


class Conditional(Expression):
    def __init__(self, condition, true_expression, false_expression):
        assert isinstance(condition, Expression)
        assert condition.sort is BUILTIN_BOOLEAN
        assert isinstance(true_expression, Expression)
        assert isinstance(false_expression, Expression)
        assert true_expression.sort is false_expression.sort
        super().__init__(true_expression.sort)
        self.condition        = condition
        self.true_expression  = true_expression
        self.false_expression = false_expression

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_conditional(self,
                                         self.condition.walk(visitor),
                                         self.true_expression.walk(visitor),
                                         self.false_expression.walk(visitor))


##############################################################################
# Quantifiers
##############################################################################

class Quantifier(Expression):
    def __init__(self, kind, variables, body):
        assert kind in ("forall", "exists")
        assert isinstance(variables, list)
        assert all(isinstance(var, Bound_Variable) for var in variables)
        assert isinstance(body, Expression)
        assert body.sort is BUILTIN_BOOLEAN
        super().__init__(BUILTIN_BOOLEAN)
        self.kind      = kind
        self.variables = variables
        self.body      = body

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        tr_variables = [var.walk(visitor) for var in self.variables]
        return visitor.visit_quantifier(self,
                                        tr_variables,
                                        self.body.walk(visitor))
