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

import cvc5

from pyvcg import smt


class CVC5_Solver(smt.VC_Solver):
    def __init__(self):
        self.solver  = cvc5.Solver()
        self.result  = None
        self.values  = {}

        self.const_mapping    = {}
        self.var_mapping      = {}
        self.enum_mapping     = {}
        self.literal_mapping  = {}
        self.function_mapping = {}
        self.sort_mapping     = {}
        self.record_mapping   = {}
        self.user_functions   = {}

        self.relevant_values  = []

    def term_to_python(self, sort, term):
        assert isinstance(sort, smt.Sort)
        assert isinstance(term, cvc5.Term)

        if isinstance(sort, smt.Enumeration):
            return str(term)
        elif isinstance(sort, smt.Record):
            assert term.getKind() == cvc5.Kind.APPLY_CONSTRUCTOR
            rv = {}
            for idx, name in enumerate(sort.components, 1):
                rv[name] = self.term_to_python(sort.components[name],
                                               term[idx])
            return rv
        elif sort.name == "Bool":
            return term.getBooleanValue()
        elif sort.name == "Int":
            return term.getIntegerValue()
        elif sort.name == "Real":
            if term.isRealValue():
                return term.getRealValue()
            else:  # pragma: no cover
                return None
        elif sort.name == "String":
            return term.getStringValue()
        elif sort.name == "Seq":
            return [self.term_to_python(sort.element_sort(), t)
                    for t in term.getSequenceValue()]
        else:
            assert False, (term.getKind(), term.__class__.__name__)

    def solve(self):
        result = self.solver.checkSat()
        if result.isSat():
            self.result = "sat"
        elif result.isUnsat():
            self.result = "unsat"
            return
        else:  # pragma: no cover
            self.result = "unknown"

        for constant in self.relevant_values:
            value = self.solver.getValue(self.const_mapping[constant])
            self.values[constant.name] = self.term_to_python(constant.sort,
                                                             value)

    def get_status(self):
        assert self.result is not None
        return self.result

    def get_values(self):
        assert self.result is not None
        return self.values

    def visit_script(self, node, logic, functions):
        assert isinstance(node, smt.Script)
        assert isinstance(logic, str)
        assert isinstance(functions, set)
        assert all(isinstance(function, str)
                   for function in functions)

        self.solver.setOption("produce-models", "true")
        self.solver.setLogic(logic)

        for function in functions:
            if function == "floor_div":
                lhs = self.solver.mkVar(self.solver.getIntegerSort(),
                                        "lhs")
                rhs = self.solver.mkVar(self.solver.getIntegerSort(),
                                        "rhs")
                fun = self.solver.defineFun(
                    function,
                    [lhs, rhs],
                    self.solver.getIntegerSort(),
                    self.solver.mkTerm(
                        cvc5.Kind.ITE,
                        self.solver.mkTerm(cvc5.Kind.LT,
                                           rhs,
                                           self.solver.mkInteger(0)),
                        self.solver.mkTerm(cvc5.Kind.INTS_DIVISION,
                                           self.solver.mkTerm(cvc5.Kind.NEG,
                                                              lhs),
                                           self.solver.mkTerm(cvc5.Kind.NEG,
                                                              rhs)),
                        self.solver.mkTerm(cvc5.Kind.INTS_DIVISION,
                                           lhs,
                                           rhs)))

            elif function == "ada_remainder":
                lhs = self.solver.mkVar(self.solver.getIntegerSort(),
                                        "lhs")
                rhs = self.solver.mkVar(self.solver.getIntegerSort(),
                                        "rhs")
                fun = self.solver.defineFun(
                    function,
                    [lhs, rhs],
                    self.solver.getIntegerSort(),
                    self.solver.mkTerm(
                        cvc5.Kind.ITE,
                        self.solver.mkTerm(cvc5.Kind.LT,
                                           lhs,
                                           self.solver.mkInteger(0)),
                        self.solver.mkTerm(
                            cvc5.Kind.NEG,
                            self.solver.mkTerm(
                                cvc5.Kind.INTS_MODULUS,
                                self.solver.mkTerm(cvc5.Kind.NEG, lhs),
                                rhs)),
                        self.solver.mkTerm(cvc5.Kind.INTS_MODULUS,
                                           lhs,
                                           rhs)))

            elif function == "to_int_rna":
                val = self.solver.mkVar(self.solver.getRealSort(),
                                        "value")
                fun = self.solver.defineFun(
                    function,
                    [val],
                    self.solver.getIntegerSort(),
                    self.solver.mkTerm(
                        cvc5.Kind.ITE,
                        self.solver.mkTerm(cvc5.Kind.GEQ,
                                           val,
                                           self.solver.mkReal(0, 1)),
                        self.solver.mkTerm(
                            cvc5.Kind.TO_INTEGER,
                            self.solver.mkTerm(
                                cvc5.Kind.ADD,
                                val,
                                self.solver.mkReal(1, 2))),
                        self.solver.mkTerm(
                            cvc5.Kind.NEG,
                            self.solver.mkTerm(
                                cvc5.Kind.TO_INTEGER,
                                self.solver.mkTerm(
                                    cvc5.Kind.SUB,
                                    self.solver.mkReal(1, 2),
                                    val)))))

            else:
                assert False, function

            self.function_mapping[function] = fun

        for statement in node.statements:
            statement.walk(self)

    def visit_constant_declaration(self, node, tr_symbol, tr_value):
        assert isinstance(node, smt.Constant_Declaration)
        assert node.symbol in self.const_mapping

        if tr_value is not None:
            self.solver.assertFormula(
                self.solver.mkTerm(cvc5.Kind.EQUAL, tr_symbol, tr_value))

        if node.is_relevant:
            self.relevant_values.append(node.symbol)

    def visit_function_declaration(self, node, tr_sort, tr_body):
        assert isinstance(node, smt.Function_Declaration)

        if tr_body is None:
            tr_params = [par.sort.walk(self)
                         for par in node.function.parameters]
            fun = self.solver.declareFun(node.function.name,
                                         tr_params,
                                         tr_sort)

        else:
            tr_params = [par.walk(self)
                         for par in node.function.parameters]
            fun = self.solver.defineFun(node.function.name,
                                        tr_params,
                                        tr_sort,
                                        tr_body)

        self.user_functions[node.function] = fun

    def visit_assertion(self, node, tr_expression):
        assert isinstance(node, smt.Assertion)

        self.solver.assertFormula(tr_expression)

    def visit_enumeration_declaration(self, node):
        assert isinstance(node, smt.Enumeration_Declaration)

        ctors = [self.solver.mkDatatypeConstructorDecl(literal)
                 for literal in node.sort.literals]

        sort = self.solver.declareDatatype(node.sort.name, *ctors)
        self.enum_mapping[node.sort] = sort

        datatype = sort.getDatatype()
        self.literal_mapping[node.sort] = {
            literal: datatype.getConstructor(literal).getTerm()
            for literal in node.sort.literals
        }

    def visit_record_declaration(self, node):
        assert isinstance(node, smt.Record_Declaration)

        ctor = self.solver.mkDatatypeConstructorDecl(node.sort.name +
                                                     "__cons")
        for name, sort in node.sort.components.items():
            ctor.addSelector(name, sort.walk(self))

        sort = self.solver.declareDatatype(node.sort.name, ctor)
        self.record_mapping[node.sort] = sort

    def visit_sort(self, node):
        assert isinstance(node, smt.Sort)

        if node.name == "Bool":
            return self.solver.getBooleanSort()
        elif node.name == "Int":
            return self.solver.getIntegerSort()
        elif node.name == "Real":
            return self.solver.getRealSort()
        elif node.name == "String":
            return self.solver.getStringSort()
        else:
            assert False

    def visit_parametric_sort(self, node, tr_parameters):
        assert isinstance(node, smt.Parametric_Sort)
        assert isinstance(tr_parameters, list)

        if node not in self.sort_mapping:
            if node.name == "Seq":
                assert len(tr_parameters) == 1
                self.sort_mapping[node] = \
                    self.solver.mkSequenceSort(tr_parameters[0])
            else:
                assert False

        return self.sort_mapping[node]

    def visit_function(self, node):
        assert isinstance(node, smt.Function)
        return self.user_functions[node]

    def visit_enumeration(self, node):
        assert isinstance(node, smt.Enumeration)
        return self.enum_mapping[node]

    def visit_record(self, node):
        assert isinstance(node, smt.Record)
        return self.record_mapping[node]

    def visit_boolean_literal(self, node, tr_sort):
        assert isinstance(node, smt.Boolean_Literal)
        return self.solver.mkBoolean(node.value)

    def visit_integer_literal(self, node, tr_sort):
        assert isinstance(node, smt.Integer_Literal)
        return self.solver.mkInteger(node.value)

    def visit_real_literal(self, node, tr_sort):
        assert isinstance(node, smt.Real_Literal)
        num, den = node.value.as_integer_ratio()
        return self.solver.mkReal(num, den)

    def visit_enumeration_literal(self, node, tr_sort):
        assert isinstance(node, smt.Enumeration_Literal)
        cons = self.literal_mapping[node.sort][node.value]
        return self.solver.mkTerm(cvc5.Kind.APPLY_CONSTRUCTOR, cons)

    def visit_string_literal(self, node, tr_sort):
        assert isinstance(node, smt.String_Literal)
        return self.solver.mkString(node.value)

    def visit_constant(self, node, tr_sort):
        assert isinstance(node, smt.Constant)

        if node not in self.const_mapping:
            self.const_mapping[node] = self.solver.mkConst(tr_sort, node.name)

        return self.const_mapping[node]

    def visit_bound_variable(self, node, tr_sort):
        assert isinstance(node, smt.Bound_Variable)

        if node not in self.var_mapping:
            self.var_mapping[node] = self.solver.mkVar(tr_sort, node.name)

        return self.var_mapping[node]

    def visit_boolean_negation(self, node, tr_sort, tr_expression):
        assert isinstance(node, smt.Boolean_Negation)

        return tr_expression.notTerm()

    def visit_conjunction(self, node, tr_sort, tr_terms):
        assert isinstance(node, smt.Conjunction)
        assert isinstance(tr_terms, list)

        return self.solver.mkTerm(cvc5.Kind.AND, *tr_terms)

    def visit_disjunction(self, node, tr_sort, tr_terms):
        assert isinstance(node, smt.Disjunction)
        assert isinstance(tr_terms, list)

        return self.solver.mkTerm(cvc5.Kind.OR, *tr_terms)

    def visit_exclusive_disjunction(self, node, tr_sort, tr_lhs, tr_rhs):
        assert isinstance(node, smt.Exclusive_Disjunction)

        return self.solver.mkTerm(cvc5.Kind.XOR, tr_lhs, tr_rhs)

    def visit_implication(self, node, tr_sort, tr_lhs, tr_rhs):
        assert isinstance(node, smt.Implication)

        return self.solver.mkTerm(cvc5.Kind.IMPLIES, tr_lhs, tr_rhs)

    def visit_comparison(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, smt.Comparison)

        kind = {"<"  : cvc5.Kind.LT,
                "<=" : cvc5.Kind.LEQ,
                ">"  : cvc5.Kind.GT,
                ">=" : cvc5.Kind.GEQ,
                "="  : cvc5.Kind.EQUAL}

        return self.solver.mkTerm(kind[node.operator], tr_lhs, tr_rhs)

    def visit_conversion_to_real(self, node, tr_value):
        assert isinstance(node, smt.Conversion_To_Real)
        return self.solver.mkTerm(cvc5.Kind.TO_REAL, tr_value)

    def visit_conversion_to_integer(self, node, tr_value):
        assert isinstance(node, smt.Conversion_To_Integer)
        if node.rounding == "rtn":
            return self.solver.mkTerm(cvc5.Kind.TO_INTEGER, tr_value)
        else:
            assert node.rounding == "rna"
            return self.solver.mkTerm(cvc5.Kind.APPLY_UF,
                                      self.function_mapping["to_int_rna"],
                                      tr_value)

    def visit_unary_int_arithmetic_op(self, node, tr_operand):
        assert isinstance(node, smt.Unary_Int_Arithmetic_Op)

        kind = {"-"   : cvc5.Kind.NEG,
                "abs" : cvc5.Kind.ABS}

        return self.solver.mkTerm(kind[node.operator], tr_operand)

    def visit_unary_real_arithmetic_op(self, node, tr_operand):
        assert isinstance(node, smt.Unary_Real_Arithmetic_Op)

        kind = {"-"   : cvc5.Kind.NEG,
                "abs" : cvc5.Kind.ABS}

        return self.solver.mkTerm(kind[node.operator], tr_operand)

    def visit_binary_int_arithmetic_op(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, smt.Binary_Int_Arithmetic_Op)

        if node.operator in ("floor_div", "ada_remainder"):
            return self.solver.mkTerm(cvc5.Kind.APPLY_UF,
                                      self.function_mapping[node.operator],
                                      tr_lhs,
                                      tr_rhs)

        kind = {"+"    : cvc5.Kind.ADD,
                "-"    : cvc5.Kind.SUB,
                "*"    : cvc5.Kind.MULT,
                "div"  : cvc5.Kind.INTS_DIVISION,
                "mod"  : cvc5.Kind.INTS_MODULUS}

        return self.solver.mkTerm(kind[node.operator], tr_lhs, tr_rhs)

    def visit_binary_real_arithmetic_op(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, smt.Binary_Real_Arithmetic_Op)

        kind = {"+" : cvc5.Kind.ADD,
                "-" : cvc5.Kind.SUB,
                "*" : cvc5.Kind.MULT,
                "/" : cvc5.Kind.DIVISION}

        return self.solver.mkTerm(kind[node.operator], tr_lhs, tr_rhs)

    def visit_string_length(self, node, tr_string):
        assert isinstance(node, smt.String_Length)
        return self.solver.mkTerm(cvc5.Kind.STRING_LENGTH, tr_string)

    def visit_string_predicate(self, node, tr_first, tr_second):
        assert isinstance(node, smt.String_Predicate)

        kind = {"contains" : cvc5.Kind.STRING_CONTAINS,
                "prefixof" : cvc5.Kind.STRING_PREFIX,
                "suffixof" : cvc5.Kind.STRING_SUFFIX}

        return self.solver.mkTerm(kind[node.operation],
                                  tr_first,
                                  tr_second)

    def visit_string_concatenation(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, smt.String_Concatenation)
        return self.solver.mkTerm(cvc5.Kind.STRING_CONCAT, tr_lhs, tr_rhs)

    def visit_sequence_length(self, node, tr_sequence):
        assert isinstance(node, smt.Sequence_Length)
        return self.solver.mkTerm(cvc5.Kind.SEQ_LENGTH, tr_sequence)

    def visit_sequence_index(self, node, tr_sequence, tr_index):
        assert isinstance(node, smt.Sequence_Index)
        return self.solver.mkTerm(cvc5.Kind.SEQ_NTH, tr_sequence, tr_index)

    def visit_sequence_contains(self, node, tr_sequence, tr_item):
        assert isinstance(node, smt.Sequence_Contains)
        return self.solver.mkTerm(cvc5.Kind.SEQ_CONTAINS,
                                  tr_sequence,
                                  self.solver.mkTerm(cvc5.Kind.SEQ_UNIT,
                                                     tr_item))

    def visit_sequence_concatenation(self, node, tr_lhs, tr_rhs):
        assert isinstance(node, smt.Sequence_Concatenation)
        return self.solver.mkTerm(cvc5.Kind.SEQ_CONCAT, tr_lhs, tr_rhs)

    def visit_record_access(self, node, tr_record):
        assert isinstance(node, smt.Record_Access)
        assert node.record.sort in self.record_mapping
        s_record_sort = self.record_mapping[node.record.sort]
        s_selector = s_record_sort.getDatatype().getSelector(node.component)
        return self.solver.mkTerm(cvc5.Kind.APPLY_SELECTOR,
                                  s_selector.getTerm(),
                                  tr_record)

    def visit_function_application(self, node, tr_function, tr_args):
        assert isinstance(node, smt.Function_Application)
        assert isinstance(tr_args, list)

        return self.solver.mkTerm(cvc5.Kind.APPLY_UF,
                                  tr_function,
                                  *tr_args)

    def visit_conditional(self, node, tr_condition, tr_true, tr_false):
        assert isinstance(node, smt.Conditional)
        return self.solver.mkTerm(cvc5.Kind.ITE,
                                  tr_condition,
                                  tr_true,
                                  tr_false)

    def visit_quantifier(self, node, tr_variables, tr_body):
        assert isinstance(node, smt.Quantifier)

        kind = {"forall" : cvc5.Kind.FORALL,
                "exists" : cvc5.Kind.EXISTS}

        return self.solver.mkTerm(kind[node.kind],
                                  self.solver.mkTerm(cvc5.Kind.VARIABLE_LIST,
                                                     *tr_variables),
                                  tr_body)
