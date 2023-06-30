import unittest

from io import StringIO
from fractions import Fraction

from pyvcg import smt


class SMTBasicTests(unittest.TestCase):
    def setUp(self):
        self.ctx = smt.CVC5_Context()
        self.out = StringIO()
        self.smtlib = smt.SMTLIB_Context(self.out)

    def write_statement(self, statement):
        self.smtlib.write_statement(statement)
        self.ctx.write_statement(statement)

    def register_relevant_value(self, constant):
        self.smtlib.register_relevant_value(constant)
        self.ctx.register_relevant_value(constant)

    def assertOutput(self, string):
        string = "\n".join(s.strip() for s in string.strip().splitlines())
        self.assertSequenceEqual(string.splitlines(),
                                 self.out.getvalue().strip().splitlines())

    def assertResult(self, status):
        assert status in ("sat", "unsat", "unknown")
        self.assertEqual(self.ctx.get_status(), status)

    def test_Simple_Free_Const(self):
        sym = smt.Constant(smt.BUILTIN_BOOLEAN, "potato")
        decl = smt.Constant_Declaration(sym, comment="this is a potato")

        decl.write_smtlib(self.out)

        self.assertOutput(
            ''';; this is a potato
               (declare-const potato Bool)''')

    def test_Simple_Const(self):
        sym = smt.Constant(smt.BUILTIN_BOOLEAN, "pot.ato")
        self.assertFalse(sym.is_static())
        self.assertFalse(sym.is_static_true())
        self.assertFalse(sym.is_static_false())

        val = smt.Boolean_Literal(False)
        self.assertTrue(val.is_static())
        self.assertFalse(val.is_static_true())
        self.assertTrue(val.is_static_false())

        decl = smt.Constant_Declaration(sym, value=val)

        decl.write_smtlib(self.out)

        self.assertOutput("(define-const |pot.ato| Bool false)")

    def test_Simple_Sat_Result(self):
        self.smtlib.write_preamble()

        sym = smt.Constant(smt.BUILTIN_INTEGER, "potato")
        decl = smt.Constant_Declaration(sym)
        self.write_statement(decl)

        self.smtlib.write_check_sat()
        self.assertOutput(
            """
            (set-logic ALL)
            (set-option :produce-models true)
            (declare-const potato Int)
            (check-sat)
            """
        )
        self.assertResult("sat")

    def test_Simple_Sat_Result_2(self):
        self.smtlib.write_preamble()

        sym = smt.Constant(smt.BUILTIN_INTEGER, "potato")
        decl = smt.Constant_Declaration(sym, value=smt.Integer_Literal(-42))
        self.write_statement(decl)
        self.register_relevant_value(sym)

        sym = smt.Constant(smt.BUILTIN_INTEGER, "kitten")
        decl = smt.Constant_Declaration(sym, value=smt.Integer_Literal(666))
        self.write_statement(decl)
        self.register_relevant_value(sym)

        self.smtlib.write_check_sat()
        self.assertOutput(
            """
            (set-logic ALL)
            (set-option :produce-models true)
            (define-const potato Int (- 42))
            (define-const kitten Int 666)
            (check-sat)
            (get-value (potato))
            (get-value (kitten))
            """
        )
        self.assertResult("sat")
        self.assertEqual(self.ctx.values["potato"], -42)
        self.assertEqual(self.ctx.values["kitten"], 666)

    def test_Simple_Unsat_Result(self):
        self.smtlib.write_preamble()

        sym = smt.Constant(smt.BUILTIN_BOOLEAN, "potato")
        decl = smt.Constant_Declaration(sym,
                                        value=smt.Boolean_Literal(False))
        self.write_statement(decl)

        ass = smt.Assertion(sym)
        self.write_statement(ass)

        self.smtlib.write_check_sat()
        self.assertOutput(
            """
            (set-logic ALL)
            (set-option :produce-models true)
            (define-const potato Bool false)
            (assert potato)
            (check-sat)
            """
        )
        self.assertResult("unsat")

    def test_Simple_Sat_Bool_Result(self):
        self.smtlib.write_preamble()

        sym = smt.Constant(smt.BUILTIN_BOOLEAN, "potato")
        decl = smt.Constant_Declaration(sym)
        self.write_statement(decl)
        self.register_relevant_value(sym)

        ass = smt.Assertion(sym)
        self.write_statement(ass)

        self.smtlib.write_check_sat()
        self.assertOutput(
            """
            (set-logic ALL)
            (set-option :produce-models true)
            (declare-const potato Bool)
            (assert potato)
            (check-sat)
            (get-value (potato))
            """
        )
        self.assertResult("sat")
        self.assertEqual(self.ctx.values["potato"], True)

    def test_Simple_Sat_Real_Free_Result(self):
        self.smtlib.write_preamble()

        sym = smt.Constant(smt.BUILTIN_REAL, "potato")
        decl = smt.Constant_Declaration(sym)
        self.write_statement(decl)
        self.register_relevant_value(sym)

        self.smtlib.write_check_sat()
        self.assertOutput(
            """
            (set-logic ALL)
            (set-option :produce-models true)
            (declare-const potato Real)
            (check-sat)
            (get-value (potato))
            """
        )
        self.assertResult("sat")
        self.assertIsInstance(self.ctx.values["potato"], Fraction)
