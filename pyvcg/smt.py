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
from io import TextIOBase
import re

import cvc5


##############################################################################
# Helper functions
##############################################################################

def escape(name):
    assert isinstance(name, str) and "|" not in name
    if re.match(r"^[a-zA-Z_][a-zA-Z0-9_]*$", name):
        return name
    else:
        return "|%s|" % name


class Context(metaclass=ABCMeta):
    def __init__(self):
        self.relevant_values = []
        self.statements      = []
        self.logic_visitor   = Logic_Visitor()
        self.logics          = set()

    def add_statement(self, statement):
        assert isinstance(statement, Statement)
        self.statements.append(statement)
        if isinstance(statement, Constant_Declaration) and \
           statement.is_relevant:
            self.relevant_values.append(statement.symbol)
        statement.walk(self.logic_visitor)

    @abstractmethod
    def generate(self):
        pass

    @abstractmethod
    def get_status(self):
        pass


class CVC5_Context(Context):
    def __init__(self):
        super().__init__()
        self.solver = cvc5.Solver()

        self.mapping = {}
        self.values  = {}

    def generate(self):
        self.solver.setOption("produce-models", "true")
        self.solver.setLogic(self.logic_visitor.get_logic_string())
        for statement in self.statements:
            statement.write_cvc5(self)

    def get_status(self):
        result = self.solver.checkSat()
        if result.isSat():
            for constant in self.relevant_values:
                value = self.solver.getValue(constant.tr_cvc5(self))
                if constant.sort.name == "Bool":
                    self.values[constant.name] = value.getBooleanValue()
                elif constant.sort.name == "Int":
                    self.values[constant.name] = value.getIntegerValue()
                elif constant.sort.name == "Real":
                    self.values[constant.name] = value.getRealValue()
                else:  # pragma: no cover
                    assert False
            return "sat"
        elif result.isUnsat():
            return "unsat"
        else:  # pragma: no cover
            return "unknown"


class SMTLIB_Context(Context):
    def __init__(self, fd):
        super().__init__()
        assert isinstance(fd, TextIOBase)
        self.fd = fd

    def generate(self):
        self.write_preamble()
        for statement in self.statements:
            statement.write_smtlib(self.fd)
        self.fd.write("(check-sat)\n")
        for constant in self.relevant_values:
            self.fd.write("(get-value (%s))\n" % constant.tr_smtlib())

    def write_preamble(self):
        self.fd.write("(set-logic %s)\n" %
                      self.logic_visitor.get_logic_string())
        self.fd.write("(set-option :produce-models true)\n")

    def get_status(self):  # pragma: no cover
        pass


class Node(metaclass=ABCMeta):
    @abstractmethod
    def walk(self, visitor):
        assert isinstance(visitor, Visitor)


class Visitor(metaclass=ABCMeta):
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
        self.logics |= tr_symbol
        if tr_value is not None:
            self.logics |= tr_value

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


##############################################################################
# Top-level items
##############################################################################

class Statement(Node, metaclass=ABCMeta):
    def __init__(self, comment):
        assert isinstance(comment, str) or comment is None
        self.comment = comment

    def write_smtlib_comment(self, fd):
        assert isinstance(fd, TextIOBase)
        if self.comment is not None:
            fd.write(";; %s\n" % self.comment)

    @abstractmethod
    def write_smtlib(self, fd):
        assert isinstance(fd, TextIOBase)

    @abstractmethod
    def write_cvc5(self, context):
        assert isinstance(context, CVC5_Context)


class Sort(Node):
    def __init__(self, name):
        assert isinstance(name, str) and "|" not in name

        self.name = name

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_sort(self)

    def tr_smtlib(self):
        return escape(self.name)

    def tr_cvc5(self, context):
        assert isinstance(context, CVC5_Context)

        if self.name == "Bool":
            return context.solver.getBooleanSort()
        elif self.name == "Int":
            return context.solver.getIntegerSort()
        elif self.name == "Real":
            return context.solver.getRealSort()
        else:
            assert False


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

    @abstractmethod
    def tr_smtlib(self):
        pass

    def tr_cvc5(self, context):
        assert isinstance(context, CVC5_Context)
        if self not in context.mapping:
            context.mapping[self] = self.gen_cvc5(context)
        return context.mapping[self]

    @abstractmethod
    def gen_cvc5(self, context):
        assert isinstance(context, CVC5_Context)


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

    def write_smtlib(self, fd):
        assert isinstance(fd, TextIOBase)

        self.write_smtlib_comment(fd)
        if self.value is not None:
            fd.write("(define-const")
        else:
            fd.write("(declare-const")
        fd.write(" %s" % self.symbol.tr_smtlib())
        fd.write(" %s" % self.symbol.sort.tr_smtlib())
        if self.value is not None:
            fd.write(" %s" % self.value.tr_smtlib())
        fd.write(")\n")

    def write_cvc5(self, context):
        assert isinstance(context, CVC5_Context)

        sym = self.symbol.tr_cvc5(context)

        if self.value is not None:
            value = self.value.tr_cvc5(context)
            context.solver.assertFormula(
                context.solver.mkTerm(cvc5.Kind.EQUAL, sym, value))


class Assertion(Statement):
    def __init__(self, expression, comment=None):
        super().__init__(comment)
        assert isinstance(expression, Expression)
        assert expression.sort is BUILTIN_BOOLEAN

        self.expression = expression

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_assertion(self, self.expression.walk(visitor))

    def write_smtlib(self, fd):
        assert isinstance(fd, TextIOBase)

        self.write_smtlib_comment(fd)
        fd.write("(assert %s)\n" % self.expression.tr_smtlib())

    def write_cvc5(self, context):
        assert isinstance(context, CVC5_Context)

        expr = self.expression.tr_cvc5(context)
        context.solver.assertFormula(expr)


##############################################################################
# Expressions
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

    def tr_smtlib(self):
        return "true" if self.value else "false"

    def gen_cvc5(self, context):
        assert isinstance(context, CVC5_Context)

        return context.solver.mkBoolean(self.value)


class Integer_Literal(Literal):
    def __init__(self, value):
        super().__init__(BUILTIN_INTEGER)
        assert isinstance(value, int)

        self.value = value

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_integer_literal(self, self.sort.walk(visitor))

    def tr_smtlib(self):
        if self.value >= 0:
            return str(self.value)
        else:
            return "(- %u)" % -self.value

    def gen_cvc5(self, context):
        assert isinstance(context, CVC5_Context)

        return context.solver.mkInteger(self.value)


class Constant(Expression):
    def __init__(self, sort, name):
        super().__init__(sort)
        assert isinstance(name, str) and "|" not in name
        self.name = name

    def walk(self, visitor):
        assert isinstance(visitor, Visitor)
        return visitor.visit_constant(self, self.sort.walk(visitor))

    def tr_smtlib(self):
        return escape(self.name)

    def gen_cvc5(self, context):
        assert isinstance(context, CVC5_Context)

        sort = self.sort.tr_cvc5(context)
        return context.solver.mkConst(sort, self.name)


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

    def tr_smtlib(self):
        return "(not %s)" % self.expression.tr_smtlib()

    def gen_cvc5(self, context):
        assert isinstance(context, CVC5_Context)

        return self.expression.tr_cvc5(context).notTerm()
