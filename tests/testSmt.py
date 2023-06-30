import unittest

from io import StringIO
from fractions import Fraction

from pyvcg import smt


class SMTBasicTests(unittest.TestCase):
    def setUp(self):
        self.ctx = smt.CVC5_Context()
        self.out = StringIO()
        self.smtlib = smt.SMTLIB_Context(self.out)

    def add_statement(self, statement):
        self.smtlib.add_statement(statement)
        self.ctx.add_statement(statement)

    def generate(self):
        self.smtlib.generate()
        self.ctx.generate()

    def assertOutput(self, string):
        string = "\n".join(s.strip() for s in string.strip().splitlines())
        self.assertSequenceEqual(string.splitlines(),
                                 self.out.getvalue().strip().splitlines())

    def assertResult(self, status, string):
        assert status in ("sat", "unsat", "unknown")

        self.generate()
        self.assertOutput(string)
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
        sym = smt.Constant(smt.BUILTIN_INTEGER, "potato")
        decl = smt.Constant_Declaration(sym, relevant=True)
        self.add_statement(decl)

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFLIA)
            (set-option :produce-models true)
            (declare-const potato Int)
            (check-sat)
            (get-value (potato))
            """
        )

    def test_Simple_Sat_Result_2(self):
        sym = smt.Constant(smt.BUILTIN_INTEGER, "potato")
        decl = smt.Constant_Declaration(sym,
                                        value    = smt.Integer_Literal(-42),
                                        relevant = True)
        self.add_statement(decl)

        sym = smt.Constant(smt.BUILTIN_INTEGER, "kitten")
        decl = smt.Constant_Declaration(sym,
                                        value    = smt.Integer_Literal(666),
                                        relevant = True)
        self.add_statement(decl)

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFLIA)
            (set-option :produce-models true)
            (define-const potato Int (- 42))
            (define-const kitten Int 666)
            (check-sat)
            (get-value (potato))
            (get-value (kitten))
            """
        )
        self.assertEqual(self.ctx.values["potato"], -42)
        self.assertEqual(self.ctx.values["kitten"], 666)

    def test_Simple_Unsat_Result(self):
        sym = smt.Constant(smt.BUILTIN_BOOLEAN, "potato")
        decl = smt.Constant_Declaration(sym,
                                        value    = smt.Boolean_Literal(False),
                                        relevant = True)
        self.add_statement(decl)

        ass = smt.Assertion(sym)
        self.add_statement(ass)

        self.assertResult(
            "unsat",
            """
            (set-logic QF_UF)
            (set-option :produce-models true)
            (define-const potato Bool false)
            (assert potato)
            (check-sat)
            (get-value (potato))
            """
        )
        self.assertEqual(self.ctx.values, {})

    def test_Simple_Sat_Bool_Result(self):
        sym = smt.Constant(smt.BUILTIN_BOOLEAN, "potato")
        decl = smt.Constant_Declaration(sym, relevant=True)
        self.add_statement(decl)

        ass = smt.Assertion(sym)
        self.add_statement(ass)

        self.assertResult(
            "sat",
            """
            (set-logic QF_UF)
            (set-option :produce-models true)
            (declare-const potato Bool)
            (assert potato)
            (check-sat)
            (get-value (potato))
            """
        )
        self.assertEqual(self.ctx.values["potato"], True)

    def test_Simple_Sat_Real_Free_Result(self):
        sym = smt.Constant(smt.BUILTIN_REAL, "potato")
        decl = smt.Constant_Declaration(sym, relevant=True)
        self.add_statement(decl)

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFLRA)
            (set-option :produce-models true)
            (declare-const potato Real)
            (check-sat)
            (get-value (potato))
            """
        )
        self.assertIsInstance(self.ctx.values["potato"], Fraction)
