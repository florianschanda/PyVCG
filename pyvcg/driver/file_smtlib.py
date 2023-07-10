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

import re

from pyvcg import smt


class SMTLIB_Generator(smt.VC_Writer):
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

    def visit_script(self, node, logic, functions):
        assert isinstance(node, smt.Script)
        assert isinstance(logic, str)
        assert isinstance(functions, set)
        assert all(isinstance(function, str)
                   for function in functions)

        script = [
            "(set-logic %s)" % logic,
            "(set-option :produce-models true)",
        ]
        for function in functions:
            if function == "floor_div":
                script.append("(define-fun floor_div"
                              " ((lhs Int) (rhs Int)) Int")
                script.append("  (ite (< rhs 0)")
                script.append("       (div (- lhs) (- rhs))")
                script.append("       (div lhs rhs)))")

            elif function == "ada_remainder":
                script.append("(define-fun ada_remainder"
                              " ((lhs Int) (rhs Int)) Int")
                script.append("  (ite (< lhs 0)")
                script.append("       (- (mod (- lhs) rhs))")
                script.append("       (mod lhs rhs)))")

            elif function == "to_int_rna":
                script.append("(define-fun to_int_rna"
                              " ((value Real)) Int")
                script.append("  (ite (>= value 0)")
                script.append("       (to_int (+ value 0.5))")
                script.append("       (- (to_int (- 0.5 value)))))")

            else:
                assert False

        script.append("")
        for statement in node.statements:
            statement.walk(self)
        script += self.lines
        script.append("(check-sat)")
        script += self.values
        script.append("(exit)")

        return "\n".join(script) + "\n"

    def visit_constant_declaration(self, node, tr_symbol, tr_value):
        assert isinstance(node, smt.Constant_Declaration)
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

    def visit_function_declaration(self, node, tr_sort, tr_body):
        assert isinstance(node, smt.Function_Declaration)

        self.emit_comment(node.comment)

        tr_name   = self.emit_name(node.function.name)

        if tr_body is None:
            tr_params = " ".join(par.sort.walk(self)
                                 for par in node.function.parameters)
            self.lines.append("(declare-fun %s (%s) %s)" % (tr_name,
                                                            tr_params,
                                                            tr_sort))

        else:
            tr_params = " ".join("(%s %s)" % (self.emit_name(par.name),
                                              par.sort.walk(self))
                                 for par in node.function.parameters)
            self.lines.append("(define-fun %s (%s) %s" % (tr_name,
                                                          tr_params,
                                                          tr_sort))
            self.lines.append("  %s)" % tr_body)

    def visit_assertion(self, node, tr_expression):
        assert isinstance(node, smt.Assertion)
        self.emit_comment(node.comment)
        self.lines.append("(assert %s)" % tr_expression)

    def visit_enumeration_declaration(self, node):
        assert isinstance(node, smt.Enumeration_Declaration)
        self.emit_comment(node.comment)
        self.lines.append("(declare-datatype %s (%s))" %
                          (self.emit_name(node.sort.name),
                           " ".join("(%s)" % literal
                                    for literal in node.sort.literals)))

    def visit_record_declaration(self, node):
        assert isinstance(node, smt.Record_Declaration)
        self.emit_comment(node.comment)
        self.lines.append("(declare-datatype %s ((%s" %
                          (self.emit_name(node.sort.name),
                           self.emit_name(node.sort.name + "__cons")))
        for name, sort in node.sort.components.items():
            self.lines.append("  (%s %s)" % (self.emit_name(name),
                                             sort.walk(self)))
        self.lines[-1] += ")))"

    def visit_sort(self, node):
        assert isinstance(node, smt.Sort)
        return self.emit_name(node.name)

    def visit_parametric_sort(self, node, tr_parameters):
        assert isinstance(node, smt.Parametric_Sort)
        assert isinstance(tr_parameters, list)
        return "(%s %s)" % (self.emit_name(node.name), " ".join(tr_parameters))

    def visit_function(self, node):
        assert isinstance(node, smt.Function)
        return self.emit_name(node.name)

    def visit_enumeration(self, node):
        assert isinstance(node, smt.Enumeration)
        return self.emit_name(node.name)

    def visit_record(self, node):
        assert isinstance(node, smt.Record)
        return self.emit_name(node.name)

    def visit_boolean_literal(self, node, tr_sort):
        assert isinstance(node, smt.Boolean_Literal)
        return "true" if node.value else "false"

    def visit_integer_literal(self, node, tr_sort):
        assert isinstance(node, smt.Integer_Literal)
        if node.value >= 0:
            return str(node.value)
        else:
            return "(- %u)" % -node.value

    def visit_real_literal(self, node, tr_sort):
        assert isinstance(node, smt.Real_Literal)
        num, den = node.value.as_integer_ratio()
        return "(/ %s %s)" % (("%u" % num if num >= 0 else "(- %u)" % num),
                              ("%u" % den if den >= 0 else "(- %u)" % den))

    def visit_enumeration_literal(self, node, tr_sort):
        assert isinstance(node, smt.Enumeration_Literal)
        return "(as %s %s)" % (node.value, tr_sort)

    def visit_string_literal(self, node, tr_sort):
        assert isinstance(node, smt.String_Literal)
        return '"%s"' % node.value

    def visit_constant(self, node, tr_sort):
        assert isinstance(node, smt.Constant)
        return self.emit_name(node.name)

    def visit_bound_variable(self, node, tr_sort):
        assert isinstance(node, smt.Bound_Variable)
        return self.emit_name(node.name)

    def visit_boolean_negation(self, node, tr_sort, tr_expression):
        assert isinstance(node, smt.Boolean_Negation)
        return "(not %s)" % tr_expression

    def visit_conjunction(self, node, tr_sort, tr_terms):
        assert isinstance(node, smt.Conjunction)
        assert isinstance(tr_terms, list)
        return "(and %s)" % " ".join(tr_terms)

    def visit_disjunction(self, node, tr_sort, tr_terms):
        assert isinstance(node, smt.Disjunction)
        assert isinstance(tr_terms, list)
        return "(or %s)" % " ".join(tr_terms)

    def visit_exclusive_disjunction(self, node, tr_sort, tr_lhs, tr_rhs):
        assert isinstance(node, smt.Exclusive_Disjunction)
        return "(xor %s %s)" % (tr_lhs, tr_rhs)

    def visit_implication(self, node, tr_sort, tr_lhs, tr_rhs):
        assert isinstance(node, smt.Implication)
        return "(=> %s %s)" % (tr_lhs, tr_rhs)

    def visit_comparison(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, smt.Comparison)
        return "(%s %s %s)" % (node.operator, tr_lhs, tr_rhs)

    def visit_conversion_to_real(self, node, tr_value):
        assert isinstance(node, smt.Conversion_To_Real)
        return "(to_real %s)" % tr_value

    def visit_conversion_to_integer(self, node, tr_value):
        assert isinstance(node, smt.Conversion_To_Integer)
        if node.rounding == "rtn":
            return "(to_int %s)" % tr_value
        else:
            assert node.rounding == "rna"
            return "(to_int_rna %s)" % tr_value

    def visit_unary_int_arithmetic_op(self, node, tr_operand):
        assert isinstance(node, smt.Unary_Int_Arithmetic_Op)
        return "(%s %s)" % (node.operator, tr_operand)

    def visit_unary_real_arithmetic_op(self, node, tr_operand):
        assert isinstance(node, smt.Unary_Real_Arithmetic_Op)
        return "(%s %s)" % (node.operator, tr_operand)

    def visit_binary_int_arithmetic_op(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, smt.Binary_Int_Arithmetic_Op)
        return "(%s %s %s)" % (node.operator, tr_lhs, tr_rhs)

    def visit_binary_real_arithmetic_op(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, smt.Binary_Real_Arithmetic_Op)
        return "(%s %s %s)" % (node.operator, tr_lhs, tr_rhs)

    def visit_string_length(self, node, tr_string):
        assert isinstance(node, smt.String_Length)
        return "(str.len %s)" % tr_string

    def visit_string_predicate(self, node, tr_first, tr_second):
        assert isinstance(node, smt.String_Predicate)
        return "(str.%s %s %s)" % (node.operation, tr_first, tr_second)

    def visit_string_concatenation(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, smt.String_Concatenation)
        return "(str.++ %s %s)" % (tr_lhs, tr_rhs)

    def visit_sequence_length(self, node, tr_sequence):
        assert isinstance(node, smt.Sequence_Length)
        return "(seq.len %s)" % tr_sequence

    def visit_sequence_index(self, node, tr_sequence, tr_index):
        assert isinstance(node, smt.Sequence_Index)
        return "(seq.nth %s %s)" % (tr_sequence, tr_index)

    def visit_sequence_contains(self, node, tr_sequence, tr_item):
        assert isinstance(node, smt.Sequence_Contains)
        return "(seq.contains %s (seq.unit %s))" % (tr_sequence, tr_item)

    def visit_sequence_concatenation(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, smt.Sequence_Concatenation)
        return "(seq.++ %s %s)" % (tr_lhs, tr_rhs)

    def visit_record_access(self, node, tr_record):
        assert isinstance(node, smt.Record_Access)
        return "(%s %s)" % (node.component, tr_record)

    def visit_function_application(self, node, tr_function, tr_args):
        assert isinstance(node, smt.Function_Application)
        assert isinstance(tr_args, list)
        return "(%s %s)" % (tr_function, " ".join(tr_args))

    def visit_conditional(self, node, tr_condition, tr_true, tr_false):
        assert isinstance(node, smt.Conditional)
        return "(ite %s %s %s)" % (tr_condition,
                                   tr_true,
                                   tr_false)

    def visit_quantifier(self, node, tr_variables, tr_body):
        assert isinstance(node, smt.Quantifier)
        return "(%s (%s)\n  %s)" % (
            node.kind,
            " ".join("(%s %s)" % (self.emit_name(var.name),
                                  var.sort.walk(self))
                     for var in node.variables),
            tr_body)
