import unittest
import subprocess

from io import StringIO
from fractions import Fraction

from pyvcg import smt


class SMTBasicTests(unittest.TestCase):
    def setUp(self):
        self.script = smt.Script()
        self.smtlib = None
        self.result = None
        self.values = None

    def assertResult(self, status, string):
        assert status in ("sat", "unsat", "unknown")

        self.smtlib = self.script.generate_vc(smt.SMTLIB_Generator())
        self.result, self.values = self.script.solve_vc(smt.CVC5_Solver())

        # Verify SMTLIB output
        string = "\n".join(s.strip() for s in string.strip().splitlines())
        self.assertSequenceEqual(
            string.splitlines(),
            list(s.strip()
                 for s in self.smtlib.strip().splitlines()))

        # Verify CVC5 result
        self.assertEqual(self.result, status)

        # Verify CVC5 result from SMTLIB input
        result = subprocess.run(["cvc5"],
                                input=string,
                                check=True,
                                capture_output=True,
                                encoding="UTF-8")
        self.assertEqual(result.stdout.splitlines()[0], status)

    def assertValue(self, name, value):
        self.assertIn(name, self.values)
        self.assertEqual(self.values[name], value)

    def test_Simple_Const(self):
        sym = smt.Constant(smt.BUILTIN_BOOLEAN, "pot.ato")
        self.assertFalse(sym.is_static())
        self.assertFalse(sym.is_static_true())
        self.assertFalse(sym.is_static_false())

        val = smt.Boolean_Literal(False)
        self.assertTrue(val.is_static())
        self.assertFalse(val.is_static_true())
        self.assertTrue(val.is_static_false())

    def test_Simple_Sat_Result(self):
        sym = smt.Constant(smt.BUILTIN_INTEGER, "potato")
        decl = smt.Constant_Declaration(sym, relevant=True)
        self.script.add_statement(decl)

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFLIA)
            (set-option :produce-models true)

            (declare-const potato Int)
            (check-sat)
            (get-value (potato))
            (exit)
            """
        )

    def test_Simple_Sat_Result_2(self):
        sym = smt.Constant(smt.BUILTIN_INTEGER, "potato")
        decl = smt.Constant_Declaration(sym,
                                        value    = smt.Integer_Literal(-42),
                                        relevant = True)
        self.script.add_statement(decl)

        sym = smt.Constant(smt.BUILTIN_INTEGER, "kitten")
        decl = smt.Constant_Declaration(sym,
                                        value    = smt.Integer_Literal(666),
                                        relevant = True)
        self.script.add_statement(decl)

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
            (exit)
            """
        )
        self.assertValue("potato", -42)
        self.assertValue("kitten", 666)

    def test_Simple_Unsat_Result(self):
        sym = smt.Constant(smt.BUILTIN_BOOLEAN, "pot.ato")
        decl = smt.Constant_Declaration(sym,
                                        value    = smt.Boolean_Literal(False),
                                        relevant = True)
        self.script.add_statement(decl)

        ass = smt.Assertion(sym, comment="Wibble")
        self.script.add_statement(ass)

        self.assertResult(
            "unsat",
            """
            (set-logic QF_UF)
            (set-option :produce-models true)

            (define-const |pot.ato| Bool false)
            ;; Wibble
            (assert |pot.ato|)
            (check-sat)
            (get-value (|pot.ato|))
            (exit)
            """
        )
        self.assertEqual(self.values, {})

    def test_Simple_Sat_Bool_Result(self):
        sym = smt.Constant(smt.BUILTIN_BOOLEAN, "potato")
        decl = smt.Constant_Declaration(sym, relevant=True)
        self.script.add_statement(decl)

        ass = smt.Assertion(sym)
        self.script.add_statement(ass)

        self.assertResult(
            "sat",
            """
            (set-logic QF_UF)
            (set-option :produce-models true)

            (declare-const potato Bool)
            (assert potato)
            (check-sat)
            (get-value (potato))
            (exit)
            """
        )
        self.assertValue("potato", True)

    def test_No_Results_If_Irrelevant(self):
        sym = smt.Constant(smt.BUILTIN_BOOLEAN, "potato")
        decl = smt.Constant_Declaration(sym)
        self.script.add_statement(decl)

        ass = smt.Assertion(sym)
        self.script.add_statement(ass)

        self.assertResult(
            "sat",
            """
            (set-logic QF_UF)
            (set-option :produce-models true)

            (declare-const potato Bool)
            (assert potato)
            (check-sat)
            (exit)
            """
        )
        self.assertEqual(self.values, {})

    def test_Simple_Sat_Real_Free_Result(self):
        sym = smt.Constant(smt.BUILTIN_REAL, "potato")
        decl = smt.Constant_Declaration(sym, relevant=True)
        self.script.add_statement(decl)

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFLRA)
            (set-option :produce-models true)

            (declare-const potato Real)
            (check-sat)
            (get-value (potato))
            (exit)
            """
        )
        self.assertIsInstance(self.values.get("potato", None), Fraction)

    def test_Simple_Int_Nonlinear_Arithmetic(self):
        sym_x = smt.Constant(smt.BUILTIN_INTEGER, "x")
        sym_y = smt.Constant(smt.BUILTIN_INTEGER, "y")
        decl = smt.Constant_Declaration(sym_x, relevant=True)
        self.script.add_statement(decl)
        decl = smt.Constant_Declaration(sym_y, relevant=True)
        self.script.add_statement(decl)

        self.script.add_statement(smt.Assertion(
            smt.Comparison(">=", sym_x, smt.Integer_Literal(1))))
        self.script.add_statement(smt.Assertion(
            smt.Comparison(">=", sym_y, smt.Integer_Literal(1))))
        self.script.add_statement(smt.Assertion(
            smt.Comparison("=",
                           smt.Binary_Int_Arithmetic_Op("*", sym_x, sym_y),
                           smt.Integer_Literal(33))))

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFNIA)
            (set-option :produce-models true)

            (declare-const x Int)
            (declare-const y Int)
            (assert (>= x 1))
            (assert (>= y 1))
            (assert (= (* x y) 33))
            (check-sat)
            (get-value (x))
            (get-value (y))
            (exit)
            """
        )

        self.assertEqual(self.values.get("x", 0) * self.values.get("y", 0), 33)

    def test_Simple_Int_Linear_Arithmetic(self):
        sym_x = smt.Constant(smt.BUILTIN_INTEGER, "x")
        sym_y = smt.Constant(smt.BUILTIN_INTEGER, "y")
        decl = smt.Constant_Declaration(sym_x, relevant=True)
        self.script.add_statement(decl)
        decl = smt.Constant_Declaration(sym_y, relevant=True)
        self.script.add_statement(decl)

        self.script.add_statement(smt.Assertion(
            smt.Comparison(">=", sym_x, smt.Integer_Literal(1))))
        self.script.add_statement(smt.Assertion(
            smt.Comparison(">=", sym_y, smt.Integer_Literal(1))))
        self.script.add_statement(smt.Assertion(
            smt.Comparison(
                "=",
                sym_x,
                smt.Binary_Int_Arithmetic_Op("*",
                                             sym_y,
                                             smt.Integer_Literal(5)))))

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFLIA)
            (set-option :produce-models true)

            (declare-const x Int)
            (declare-const y Int)
            (assert (>= x 1))
            (assert (>= y 1))
            (assert (= x (* y 5)))
            (check-sat)
            (get-value (x))
            (get-value (y))
            (exit)
            """
        )

        self.assertEqual(self.values.get("x", 0), self.values.get("y", 0) * 5)

    def test_Logical_Connectives(self):
        sym_a = smt.Constant(smt.BUILTIN_BOOLEAN, "a")
        sym_b = smt.Constant(smt.BUILTIN_BOOLEAN, "b")
        sym_c = smt.Constant(smt.BUILTIN_BOOLEAN, "c")

        self.script.add_statement(
            smt.Constant_Declaration(sym_a, relevant=True))
        self.script.add_statement(
            smt.Constant_Declaration(sym_b, relevant=True))
        self.script.add_statement(
            smt.Constant_Declaration(sym_c, relevant=True))

        self.script.add_statement(
            smt.Assertion(
                smt.Conjunction(
                    smt.Disjunction(sym_a, sym_b),
                    smt.Disjunction(sym_b, sym_c))))
        self.script.add_statement(
            smt.Assertion(
                smt.Implication(sym_a, sym_c)))

        self.assertResult(
            "sat",
            """
            (set-logic QF_UF)
            (set-option :produce-models true)

            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (assert (and (or a b) (or b c)))
            (assert (=> a c))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (get-value (c))
            (exit)
            """
        )

    def test_Enum_Simple(self):
        enum = smt.Enumeration("Colour")
        enum.add_literal("red")
        enum.add_literal("green")
        enum.add_literal("blue")

        self.script.add_statement(
            smt.Enumeration_Declaration(enum))

        sym_a = smt.Constant(enum, "a")
        self.script.add_statement(
            smt.Constant_Declaration(sym_a, relevant=True))

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFDT)
            (set-option :produce-models true)

            (declare-datatype Colour ((red) (green) (blue)))
            (declare-const a Colour)
            (check-sat)
            (get-value (a))
            (exit)
            """
        )
        self.assertIn(self.values["a"], enum.literals)

    def test_Enum_Exclusion(self):
        enum = smt.Enumeration("Team")
        enum.add_literal("green")
        enum.add_literal("purple")

        self.script.add_statement(
            smt.Enumeration_Declaration(enum))

        sym_a = smt.Constant(enum, "a")
        sym_b = smt.Constant(enum, "b")
        self.script.add_statement(
            smt.Constant_Declaration(sym_a, relevant=True))
        self.script.add_statement(
            smt.Constant_Declaration(sym_b, relevant=True))

        self.script.add_statement(
            smt.Assertion(
                smt.Boolean_Negation(
                    smt.Comparison("=", sym_a, sym_b))))

        self.script.add_statement(
            smt.Assertion(
                smt.Comparison("=",
                               sym_a,
                               smt.Enumeration_Literal(enum, "green"))))

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFDT)
            (set-option :produce-models true)

            (declare-datatype Team ((green) (purple)))
            (declare-const a Team)
            (declare-const b Team)
            (assert (not (= a b)))
            (assert (= a (as green Team)))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (exit)
            """
        )
        self.assertValue("a", "green")
        self.assertValue("b", "purple")

    def test_Basic_Division(self):
        sym_a = smt.Constant(smt.BUILTIN_INTEGER, "a")
        sym_b = smt.Constant(smt.BUILTIN_INTEGER, "b")
        self.script.add_statement(
            smt.Constant_Declaration(sym_a,
                                     smt.Integer_Literal(5),
                                     relevant=True))
        self.script.add_statement(
            smt.Constant_Declaration(sym_b,
                                     smt.Integer_Literal(-2),
                                     relevant=True))

        sym_result = smt.Constant(smt.BUILTIN_INTEGER, "result")
        self.script.add_statement(
            smt.Constant_Declaration(
                sym_result,
                smt.Binary_Int_Arithmetic_Op("div", sym_a, sym_b),
                relevant=True))

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFNIA)
            (set-option :produce-models true)

            (define-const a Int 5)
            (define-const b Int (- 2))
            (define-const result Int (div a b))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (get-value (result))
            (exit)
            """
        )
        self.assertValue("result", -2)

    def test_Floor_Division(self):
        sym_a = smt.Constant(smt.BUILTIN_INTEGER, "a")
        sym_b = smt.Constant(smt.BUILTIN_INTEGER, "b")
        self.script.add_statement(
            smt.Constant_Declaration(sym_a,
                                     smt.Integer_Literal(5),
                                     relevant=True))
        self.script.add_statement(
            smt.Constant_Declaration(
                sym_b,
                smt.Unary_Int_Arithmetic_Op("-", smt.Integer_Literal(2)),
                relevant=True))

        sym_result = smt.Constant(smt.BUILTIN_INTEGER, "result")
        self.script.add_statement(
            smt.Constant_Declaration(
                sym_result,
                smt.Binary_Int_Arithmetic_Op("floor_div", sym_a, sym_b),
                relevant=True))

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFNIA)
            (set-option :produce-models true)
            (define-fun floor_div ((lhs Int) (rhs Int)) Int
              (ite (< rhs 0)
                   (div (- lhs) (- rhs))
                   (div lhs rhs)))

            (define-const a Int 5)
            (define-const b Int (- 2))
            (define-const result Int (floor_div a b))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (get-value (result))
            (exit)
            """
        )
        self.assertValue("result", -3)

    def test_Ada_Remainder(self):
        sym_a = smt.Constant(smt.BUILTIN_INTEGER, "a")
        sym_b = smt.Constant(smt.BUILTIN_INTEGER, "b")
        self.script.add_statement(
            smt.Constant_Declaration(sym_a,
                                     smt.Integer_Literal(-13),
                                     relevant=True))
        self.script.add_statement(
            smt.Constant_Declaration(sym_b,
                                     smt.Integer_Literal(-5),
                                     relevant=True))

        sym_result = smt.Constant(smt.BUILTIN_INTEGER, "result")
        self.script.add_statement(
            smt.Constant_Declaration(
                sym_result,
                smt.Binary_Int_Arithmetic_Op("ada_remainder", sym_a, sym_b),
                relevant=True))

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFNIA)
            (set-option :produce-models true)
            (define-fun ada_remainder ((lhs Int) (rhs Int)) Int
              (ite (< lhs 0)
                   (- (mod (- lhs) rhs))
                   (mod lhs rhs)))

            (define-const a Int (- 13))
            (define-const b Int (- 5))
            (define-const result Int (ada_remainder a b))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (get-value (result))
            (exit)
            """
        )
        self.assertValue("result", -3)
