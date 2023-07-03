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
import re

import cvc5


##############################################################################
# Abstract Visitors
##############################################################################

class Visitor(metaclass=ABCMeta):
    @abstractmethod
    def visit_script(self, node, logic):
        assert isinstance(node, Script)
        assert isinstance(logic, str)

    @abstractmethod
    def visit_sort(self, node):
        assert isinstance(node, Sort)

    @abstractmethod
    def visit_constant_declaration(self, node, tr_symbol, tr_value):
        assert isinstance(node, Constant_Declaration)

    @abstractmethod
    def visit_assertion(self, node, tr_expression):
        assert isinstance(node, Assertion)

    @abstractmethod
    def visit_boolean_literal(self, node, tr_sort):
        assert isinstance(node, Boolean_Literal)

    @abstractmethod
    def visit_integer_literal(self, node, tr_sort):
        assert isinstance(node, Integer_Literal)

    @abstractmethod
    def visit_constant(self, node, tr_sort):
        assert isinstance(node, Constant)

    @abstractmethod
    def visit_boolean_negation(self, node, tr_sort, tr_expression):
        assert isinstance(node, Boolean_Negation)

    @abstractmethod
    def visit_comparison(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Comparison)

    @abstractmethod
    def visit_binary_int_arithmetic_op(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Binary_Int_Arithmetic_Op)


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
        self.logics = set()

    def get_logic_string(self):
        allowed_logics = set(["quant", "int", "real", "nonlinear"])

        assert not self.logics or self.logics < allowed_logics, \
            "%s is not a permitted logic" % (self.logics - allowed_logics)

        if "quant" in self.logics:  # pragma: no cover
            logic = ""
        else:
            logic = "QF_"

        logic += "UF"

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

        return logic

    def visit_script(self, node, logic):  # pragma: no cover
        assert isinstance(node, Script)
        assert isinstance(logic, str)
        assert False

    def visit_sort(self, node):
        assert isinstance(node, Sort)
        if node.name == "Bool":
            return set()
        elif node.name == "Int":
            return {"int"}
        elif node.name == "Real":
            return {"real"}
        else:
            assert False, "unexpected base sort %s" % node.name

    def visit_constant_declaration(self, node, tr_symbol, tr_value):
        assert isinstance(node, Constant_Declaration)
        assert isinstance(tr_symbol, set)
        assert isinstance(tr_value, set) or tr_value is None
        if tr_value is not None:
            self.logics |= tr_value
        self.logics |= tr_symbol

    def visit_assertion(self, node, tr_expression):
        assert isinstance(node, Assertion)
        assert isinstance(tr_expression, set)
        self.logics |= tr_expression

    def visit_boolean_literal(self, node, tr_sort):
        assert isinstance(node, Boolean_Literal)
        assert isinstance(tr_sort, set)
        return tr_sort

    def visit_integer_literal(self, node, tr_sort):
        assert isinstance(node, Integer_Literal)
        assert isinstance(tr_sort, set)
        return tr_sort

    def visit_constant(self, node, tr_sort):
        assert isinstance(node, Constant)
        assert isinstance(tr_sort, set)
        return tr_sort

    def visit_boolean_negation(self, node, tr_sort, tr_expression):
        assert isinstance(node, Boolean_Negation)
        assert isinstance(tr_sort, set)
        assert isinstance(tr_expression, set)
        return tr_sort | tr_expression

    def visit_comparison(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Comparison)
        return tr_lhs | tr_rhs

    def visit_binary_int_arithmetic_op(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Binary_Int_Arithmetic_Op)
        nonlinear = node.operator in ("+", "-") or \
            (node.operator == "*" and (node.lhs.is_static() or
                                       node.rhs.is_static())) or \
            (node.lhs.is_static() and node.rhs.is_static())
        if nonlinear:
            return tr_lhs | tr_rhs
        else:
            return {"nonlinear"} | tr_lhs | tr_rhs


class SMTLIB_Generator(VC_Writer):
    def __init__(self):
        self.lines  = []
        self.values = []

    def emit_comment(self, comment):
        assert isinstance(comment, str) or comment is None
        if comment is not None:
            self.lines.append(";; %s" % comment)

    def emit_name(self, name):
        assert isinstance(name, str) and "|" not in name
        if re.match(r"^[a-zA-Z_][a-zA-Z0-9_]*$", name):
            return name
        else:
            return "|%s|" % name

    def visit_script(self, node, logic):
        assert isinstance(node, Script)
        assert isinstance(logic, str)

        script = [
            "(set-logic %s)" % logic,
            "(set-option :produce-models true)",
            "",
        ]
        for statement in node.statements:
            statement.walk(self)
        script += self.lines
        script.append("(check-sat)")
        script += self.values
        script.append("(exit)")

        return "\n".join(script) + "\n"

    def visit_sort(self, node):
        assert isinstance(node, Sort)
        return node.name

    def visit_constant_declaration(self, node, tr_symbol, tr_value):
        assert isinstance(node, Constant_Declaration)
        assert isinstance(tr_symbol, str)
        assert isinstance(tr_value, str) or tr_value is None

        if node.is_relevant:
            self.values.append("(get-value (%s))" % tr_symbol)

        tr_sort = node.symbol.sort.walk(self)
        self.emit_comment(node.comment)
        if tr_value is None:
            self.lines.append("(declare-const %s %s)" % (tr_symbol, tr_sort))
        else:
            self.lines.append("(define-const %s %s %s)" % (tr_symbol,
                                                           tr_sort,
                                                           tr_value))

    def visit_assertion(self, node, tr_expression):
        assert isinstance(node, Assertion)
        self.emit_comment(node.comment)
        self.lines.append("(assert %s)" % tr_expression)

    def visit_boolean_literal(self, node, tr_sort):
        assert isinstance(node, Boolean_Literal)
        return "true" if node.value else "false"

    def visit_integer_literal(self, node, tr_sort):
        assert isinstance(node, Integer_Literal)
        if node.value >= 0:
            return str(node.value)
        else:
            return "(- %u)" % -node.value

    def visit_constant(self, node, tr_sort):
        assert isinstance(node, Constant)
        return self.emit_name(node.name)

    def visit_boolean_negation(self, node, tr_sort, tr_expression):
        assert isinstance(node, Boolean_Negation)
        return "(not %s)" % tr_expression

    def visit_comparison(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Comparison)

        return "(%s %s %s)" % (node.operator, tr_lhs, tr_rhs)

    def visit_binary_int_arithmetic_op(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Binary_Int_Arithmetic_Op)

        return "(%s %s %s)" % (node.operator, tr_lhs, tr_rhs)


class CVC5_Solver(VC_Solver):
    def __init__(self):
        self.solver  = cvc5.Solver()
        self.result  = None
        self.values  = {}

        self.const_mapping = {}

        self.relevant_values = []

    def solve(self):
        result = self.solver.checkSat()
        if result.isSat():
            self.result = "sat"
        elif result.isUnsat():
            self.result = "unsat"
            return
        else:  # pragma: no cover
            self.result = "unknown"
            return

        for constant in self.relevant_values:
            value = self.solver.getValue(self.const_mapping[constant])
            if constant.sort.name == "Bool":
                self.values[constant.name] = value.getBooleanValue()
            elif constant.sort.name == "Int":
                self.values[constant.name] = value.getIntegerValue()
            elif constant.sort.name == "Real":
                self.values[constant.name] = value.getRealValue()
            else:  # pragma: no cover
                assert False

    def get_status(self):
        assert self.result is not None
        return self.result

    def get_values(self):
        assert self.result is not None
        return self.values

    def visit_script(self, node, logic):
        assert isinstance(node, Script)
        assert isinstance(logic, str)

        self.solver.setOption("produce-models", "true")
        self.solver.setLogic(logic)

        for statement in node.statements:
            statement.walk(self)

    def visit_sort(self, node):
        assert isinstance(node, Sort)

        if node.name == "Bool":
            return self.solver.getBooleanSort()
        elif node.name == "Int":
            return self.solver.getIntegerSort()
        elif node.name == "Real":
            return self.solver.getRealSort()
        else:
            assert False

    def visit_constant_declaration(self, node, tr_symbol, tr_value):
        assert isinstance(node, Constant_Declaration)
        assert node.symbol in self.const_mapping

        if tr_value is not None:
            self.solver.assertFormula(
                self.solver.mkTerm(cvc5.Kind.EQUAL, tr_symbol, tr_value))

        if node.is_relevant:
            self.relevant_values.append(node.symbol)

    def visit_assertion(self, node, tr_expression):
        assert isinstance(node, Assertion)

        self.solver.assertFormula(tr_expression)

    def visit_boolean_literal(self, node, tr_sort):
        assert isinstance(node, Boolean_Literal)

        return self.solver.mkBoolean(node.value)

    def visit_integer_literal(self, node, tr_sort):
        assert isinstance(node, Integer_Literal)

        return self.solver.mkInteger(node.value)

    def visit_constant(self, node, tr_sort):
        assert isinstance(node, Constant)

        if node not in self.const_mapping:
            self.const_mapping[node] = self.solver.mkConst(tr_sort, node.name)

        return self.const_mapping[node]

    def visit_boolean_negation(self, node, tr_sort, tr_expression):
        assert isinstance(node, Boolean_Negation)

        return tr_expression.notTerm()

    def visit_comparison(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Comparison)

        kind = {"<"  : cvc5.Kind.LT,
                "<=" : cvc5.Kind.LEQ,
                ">"  : cvc5.Kind.GT,
                ">=" : cvc5.Kind.GEQ,
                "="  : cvc5.Kind.EQUAL}

        return self.solver.mkTerm(kind[node.operator], tr_lhs, tr_rhs)

    def visit_binary_int_arithmetic_op(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, Binary_Int_Arithmetic_Op)

        kind = {"+"    : cvc5.Kind.ADD,
                "-"    : cvc5.Kind.SUB,
                "*"    : cvc5.Kind.MULT,
                "div"  : cvc5.Kind.INTS_DIVISION,
                "mod"  : cvc5.Kind.INTS_MODULUS}

        return self.solver.mkTerm(kind[node.operator], tr_lhs, tr_rhs)


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
                                    self.logic.get_logic_string())

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


BUILTIN_BOOLEAN = Sort("Bool")
BUILTIN_INTEGER = Sort("Int")
BUILTIN_REAL    = Sort("Real")


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


class Assertion(Statement):
    def __init__(self, expression, comment=None):
        super().__init__(comment)
        assert isinstance(expression, Expression)
        assert expression.sort is BUILTIN_BOOLEAN

        self.expression = expression

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_assertion(self, self.expression.walk(visitor))


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


class Constant(Expression):
    def __init__(self, sort, name):
        super().__init__(sort)
        assert isinstance(name, str) and "|" not in name
        self.name = name

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_constant(self, self.sort.walk(visitor))


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
# Arithmetic
##############################################################################

class Binary_Int_Arithmetic_Op(Expression):
    def __init__(self, operator, lhs, rhs):
        assert operator in ("+", "-", "*", "div", "mod")
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
