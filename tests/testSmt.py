import unittest
import subprocess

from io import StringIO
from fractions import Fraction

from pyvcg import smt
from pyvcg.driver.file_smtlib import SMTLIB_Generator
from pyvcg.driver.cvc5_api import CVC5_Solver


class SMTBasicTests(unittest.TestCase):
    def setUp(self):
        self.script = smt.Script()
        self.smtlib = None
        self.result = None
        self.values = None

    def assertResult(self, status, string):
        assert status in ("sat", "unsat", "unknown")

        self.smtlib = self.script.generate_vc(SMTLIB_Generator())
        self.result, self.values = self.script.solve_vc(CVC5_Solver())

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
            (set-logic QF_LIA)
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
            (set-logic QF_LIA)
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
            (set-logic QF_SAT)
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
            (set-logic QF_SAT)
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
            (set-logic QF_SAT)
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
            (set-logic QF_LRA)
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
            (set-logic QF_NIA)
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
            (set-logic QF_LIA)
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
        sym_d = smt.Constant(smt.BUILTIN_BOOLEAN, "d")

        self.script.add_statement(
            smt.Constant_Declaration(sym_a, relevant=True))
        self.script.add_statement(
            smt.Constant_Declaration(sym_b, relevant=True))
        self.script.add_statement(
            smt.Constant_Declaration(sym_c, relevant=True))
        self.script.add_statement(
            smt.Constant_Declaration(sym_d, relevant=True))

        self.script.add_statement(
            smt.Assertion(
                smt.Conjunction(
                    smt.Disjunction(sym_a, sym_b),
                    smt.Disjunction(sym_b, sym_c))))
        self.script.add_statement(
            smt.Assertion(
                smt.Implication(sym_a, sym_c)))
        self.script.add_statement(
            smt.Assertion(
                smt.Exclusive_Disjunction(sym_a, sym_d)))

        self.assertResult(
            "sat",
            """
            (set-logic QF_SAT)
            (set-option :produce-models true)

            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const c Bool)
            (declare-const d Bool)
            (assert (and (or a b) (or b c)))
            (assert (=> a c))
            (assert (xor a d))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (get-value (c))
            (get-value (d))
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
            (set-logic QF_DT)
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
            (set-logic QF_DT)
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
            (set-logic QF_NIA)
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

    def test_String_Predicates(self):
        sym_a = smt.Constant(smt.BUILTIN_STRING, "a")
        sym_b = smt.Constant(smt.BUILTIN_STRING, "b")
        self.script.add_statement(
            smt.Constant_Declaration(sym_a,
                                     relevant=True))
        self.script.add_statement(
            smt.Constant_Declaration(sym_b,
                                     smt.String_Concatenation(sym_a, sym_a),
                                     relevant=True))

        self.script.add_statement(
            smt.Assertion(
                smt.Comparison(">=",
                               smt.String_Length(sym_a),
                               smt.Integer_Literal(10))))

        self.script.add_statement(
            smt.Assertion(
                smt.String_Predicate("prefixof",
                                     smt.String_Literal("foo"),
                                     sym_a)))

        self.script.add_statement(
            smt.Assertion(
                smt.String_Predicate("suffixof",
                                     smt.String_Literal("bar"),
                                     sym_a)))

        self.script.add_statement(
            smt.Assertion(
                smt.Boolean_Negation(
                    smt.String_Predicate("contains",
                                         sym_a,
                                         smt.String_Literal("A")))))

        self.assertResult(
            "sat",
            """
            (set-logic QF_SLIA)
            (set-option :produce-models true)

            (declare-const a String)
            (define-const b String (str.++ a a))
            (assert (>= (str.len a) 10))
            (assert (str.prefixof "foo" a))
            (assert (str.suffixof "bar" a))
            (assert (not (str.contains a "A")))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (exit)
            """
        )
        self.assertEqual(len(self.values["a"]), 10)
        self.assertTrue(self.values["a"].startswith("foo"),
                        self.values["a"])
        self.assertTrue(self.values["a"].endswith("bar"),
                        self.values["a"])
        self.assertNotIn("A", self.values["a"])
        self.assertValue("b", self.values["a"] + self.values["a"])

    def test_Sequences(self):
        sort = smt.Sequence_Sort(smt.BUILTIN_INTEGER)
        sym_a = smt.Constant(sort, "a")
        self.script.add_statement(
            smt.Constant_Declaration(sym_a,
                                     relevant=True))

        sym_b = smt.Constant(sort, "b")
        self.script.add_statement(
            smt.Constant_Declaration(sym_b,
                                     smt.Sequence_Concatenation(sym_a, sym_a),
                                     relevant=True))

        self.script.add_statement(
            smt.Assertion(
                smt.Comparison(">",
                               smt.Sequence_Length(sym_a),
                               smt.Integer_Literal(10))))
        self.script.add_statement(
            smt.Assertion(
                smt.Sequence_Contains(sym_a, smt.Integer_Literal(42))))
        self.script.add_statement(
            smt.Assertion(
                smt.Comparison("=",
                               smt.Sequence_Index(sym_a,
                                                  smt.Integer_Literal(3)),
                               smt.Integer_Literal(123))))

        self.assertResult(
            "sat",
            """
            (set-logic QF_SLIA)
            (set-option :produce-models true)

            (declare-const a (Seq Int))
            (define-const b (Seq Int) (seq.++ a a))
            (assert (> (seq.len a) 10))
            (assert (seq.contains a (seq.unit 42)))
            (assert (= (seq.nth a 3) 123))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (exit)
            """
        )
        self.assertGreater(len(self.values["a"]), 10)
        self.assertIn(42, self.values["a"])
        self.assertEqual(self.values["a"][3], 123)
        self.assertSequenceEqual(self.values["a"] + self.values["a"],
                                 self.values["b"])

    def test_Real_Operations(self):
        sym_a = smt.Constant(smt.BUILTIN_REAL, "a")
        sym_b = smt.Constant(smt.BUILTIN_REAL, "b")
        self.script.add_statement(
            smt.Constant_Declaration(sym_a,
                                     relevant=True))
        self.script.add_statement(
            smt.Constant_Declaration(sym_b,
                                     relevant=True))
        self.script.add_statement(
            smt.Assertion(
                smt.Comparison(">",
                               smt.Unary_Real_Arithmetic_Op(
                                   "abs",
                                   smt.Binary_Real_Arithmetic_Op("+",
                                                                 sym_a,
                                                                 sym_b)),
                               smt.Real_Literal(10))))
        self.script.add_statement(
            smt.Assertion(
                smt.Comparison("=",
                               smt.Binary_Real_Arithmetic_Op("*",
                                                             sym_a,
                                                             sym_b),
                               smt.Real_Literal(Fraction(7, 3)))))

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFNRA)
            (set-option :produce-models true)

            (declare-const a Real)
            (declare-const b Real)
            (assert (> (abs (+ a b)) (/ 10 1)))
            (assert (= (* a b) (/ 7 3)))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (exit)
            """
        )
        self.assertGreater(abs(self.values["a"] + self.values["b"]), 10)
        self.assertEqual(self.values["a"] * self.values["b"], Fraction(7, 3))

    def test_Real_Conversions_To_Real(self):
        sym_a = smt.Constant(smt.BUILTIN_REAL, "a")
        self.script.add_statement(
            smt.Constant_Declaration(sym_a,
                                     smt.Conversion_To_Real(
                                         smt.Integer_Literal(-1)),
                                     relevant=True))

        sym_b = smt.Constant(smt.BUILTIN_REAL, "b")
        self.script.add_statement(
            smt.Constant_Declaration(sym_b,
                                     smt.Conversion_To_Real(
                                         smt.Integer_Literal(1)),
                                     relevant=True))

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFLIRA)
            (set-option :produce-models true)

            (define-const a Real (to_real (- 1)))
            (define-const b Real (to_real 1))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (exit)
            """
        )
        self.assertValue("a", Fraction(-1, 1))
        self.assertValue("b", Fraction(1))

    def test_Real_Conversions_To_Int(self):
        sym_a = smt.Constant(smt.BUILTIN_INTEGER, "a")
        self.script.add_statement(
            smt.Constant_Declaration(sym_a,
                                     smt.Conversion_To_Integer(
                                         "rtn",
                                         smt.Real_Literal(Fraction(1, 2))),
                                     relevant=True))

        sym_b = smt.Constant(smt.BUILTIN_INTEGER, "b")
        self.script.add_statement(
            smt.Constant_Declaration(sym_b,
                                     smt.Conversion_To_Integer(
                                         "rna",
                                         smt.Real_Literal(Fraction(1, 2))),
                                     relevant=True))

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFLIRA)
            (set-option :produce-models true)
            (define-fun to_int_rna ((value Real)) Int
              (ite (>= value 0)
                   (to_int (+ value 0.5))
                   (- (to_int (- 0.5 value)))))

            (define-const a Int (to_int (/ 1 2)))
            (define-const b Int (to_int_rna (/ 1 2)))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (exit)
            """
        )
        self.assertValue("a", 0)
        self.assertValue("b", 1)

    def test_Real_Operations(self):
        sym_a = smt.Constant(smt.BUILTIN_REAL, "a")
        sym_b = smt.Constant(smt.BUILTIN_REAL, "b")
        self.script.add_statement(
            smt.Constant_Declaration(sym_a,
                                     relevant=True))
        self.script.add_statement(
            smt.Constant_Declaration(sym_b,
                                     relevant=True))
        self.script.add_statement(
            smt.Assertion(
                smt.Comparison(">",
                               smt.Unary_Real_Arithmetic_Op(
                                   "abs",
                                   smt.Binary_Real_Arithmetic_Op("+",
                                                                 sym_a,
                                                                 sym_b)),
                               smt.Real_Literal(10))))
        self.script.add_statement(
            smt.Assertion(
                smt.Comparison("=",
                               smt.Binary_Real_Arithmetic_Op("*",
                                                             sym_a,
                                                             sym_b),
                               smt.Real_Literal(Fraction(7, 3)))))

        self.assertResult(
            "sat",
            """
            (set-logic QF_NRA)
            (set-option :produce-models true)

            (declare-const a Real)
            (declare-const b Real)
            (assert (> (abs (+ a b)) (/ 10 1)))
            (assert (= (* a b) (/ 7 3)))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (exit)
            """
        )
        self.assertGreater(abs(self.values["a"] + self.values["b"]), 10)
        self.assertEqual(self.values["a"] * self.values["b"], Fraction(7, 3))

    def test_Real_Conversions_To_Real(self):
        sym_a = smt.Constant(smt.BUILTIN_REAL, "a")
        self.script.add_statement(
            smt.Constant_Declaration(sym_a,
                                     smt.Conversion_To_Real(
                                         smt.Integer_Literal(-1)),
                                     relevant=True))

        sym_b = smt.Constant(smt.BUILTIN_REAL, "b")
        self.script.add_statement(
            smt.Constant_Declaration(sym_b,
                                     smt.Conversion_To_Real(
                                         smt.Integer_Literal(1)),
                                     relevant=True))

        self.assertResult(
            "sat",
            """
            (set-logic QF_LIRA)
            (set-option :produce-models true)

            (define-const a Real (to_real (- 1)))
            (define-const b Real (to_real 1))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (exit)
            """
        )
        self.assertValue("a", Fraction(-1, 1))
        self.assertValue("b", Fraction(1))

    def test_Quantification(self):
        sym_s = smt.Constant(smt.Sequence_Sort(smt.BUILTIN_INTEGER),
                             "arr")
        self.script.add_statement(
            smt.Constant_Declaration(sym_s,
                                     relevant=True))
        self.script.add_statement(
            smt.Assertion(smt.Comparison("=",
                                         smt.Sequence_Length(sym_s),
                                         smt.Integer_Literal(10))))

        s_var = smt.Bound_Variable(smt.BUILTIN_INTEGER, "i")
        s_guard = smt.Conjunction(
            smt.Comparison(">=", s_var, smt.Integer_Literal(3)),
            smt.Comparison("<=", s_var, smt.Integer_Literal(6)))
        s_body = smt.Comparison("=",
                                smt.Sequence_Index(sym_s,
                                                   s_var),
                                smt.Integer_Literal(42))

        s_quant = smt.Quantifier("forall",
                                 [s_var],
                                 smt.Implication(s_guard, s_body))
        self.script.add_statement(smt.Assertion(s_quant))

        self.assertResult(
            "unknown",
            """
            (set-logic SLIA)
            (set-option :produce-models true)

            (declare-const arr (Seq Int))
            (assert (= (seq.len arr) 10))
            (assert (forall ((i Int))
              (=> (and (>= i 3) (<= i 6)) (= (seq.nth arr i) 42))))
            (check-sat)
            (get-value (arr))
            (exit)
            """
        )

    def test_Records(self):
        s_sort = smt.Record("Kitten")
        s_sort.add_component("legs", smt.BUILTIN_INTEGER)
        s_sort.add_component("name", smt.BUILTIN_STRING)
        self.script.add_statement(smt.Record_Declaration(s_sort))

        s_rec = smt.Constant(s_sort, "a")
        self.script.add_statement(
            smt.Constant_Declaration(s_rec,
                                     relevant=True))
        self.script.add_statement(
            smt.Assertion(
                smt.Comparison("=",
                               smt.Record_Access(s_rec, "legs"),
                               smt.Integer_Literal(4))))
        self.script.add_statement(
            smt.Assertion(
                smt.Comparison("=",
                               smt.Record_Access(s_rec, "name"),
                               smt.String_Literal("fuzzy"))))

        self.assertResult(
            "sat",
            """
            (set-logic QF_DTSLIA)
            (set-option :produce-models true)

            (declare-datatype Kitten ((Kitten__cons
              (legs Int)
              (name String))))
            (declare-const a Kitten)
            (assert (= (legs a) 4))
            (assert (= (name a) "fuzzy"))
            (check-sat)
            (get-value (a))
            (exit)
            """
        )
        self.assertValue("a", {"name": "fuzzy",
                               "legs": 4})

    def test_UF_No_Body(self):
        s_par = smt.Bound_Variable(smt.BUILTIN_INTEGER, "x")
        s_fun = smt.Function("potato", smt.BUILTIN_INTEGER, s_par)
        self.script.add_statement(smt.Function_Declaration(s_fun))

        self.script.add_statement(
            smt.Assertion(
                smt.Comparison("=",
                               smt.Function_Application(
                                   s_fun,
                                   smt.Integer_Literal(3)),
                               smt.Integer_Literal(42))))

        sym_a = smt.Constant(smt.BUILTIN_INTEGER, "a")
        self.script.add_statement(
            smt.Constant_Declaration(sym_a,
                                     smt.Integer_Literal(3),
                                     relevant=True))
        sym_b = smt.Constant(smt.BUILTIN_INTEGER, "b")
        self.script.add_statement(
            smt.Constant_Declaration(sym_b,
                                     smt.Function_Application(s_fun, sym_a),
                                     relevant=True))

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFLIA)
            (set-option :produce-models true)

            (declare-fun potato (Int) Int)
            (assert (= (potato 3) 42))
            (define-const a Int 3)
            (define-const b Int (potato a))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (exit)
            """
        )
        self.assertValue("b", 42)

    def test_UF_With_Body(self):
        s_par = smt.Bound_Variable(smt.BUILTIN_INTEGER, "x")
        s_fun = smt.Function("potato", smt.BUILTIN_INTEGER, s_par)
        s_fun.define_body(
            smt.Binary_Int_Arithmetic_Op("*",
                                         s_par,
                                         smt.Integer_Literal(2)))
        self.script.add_statement(smt.Function_Declaration(s_fun))

        sym_a = smt.Constant(smt.BUILTIN_INTEGER, "a")
        self.script.add_statement(
            smt.Constant_Declaration(sym_a,
                                     relevant=True))
        self.script.add_statement(
            smt.Assertion(smt.Comparison(">=",
                                         sym_a,
                                         smt.Integer_Literal(50))))
        sym_b = smt.Constant(smt.BUILTIN_INTEGER, "b")
        self.script.add_statement(
            smt.Constant_Declaration(sym_b,
                                     smt.Function_Application(s_fun, sym_a),
                                     relevant=True))

        self.assertResult(
            "sat",
            """
            (set-logic QF_UFLIA)
            (set-option :produce-models true)

            (define-fun potato ((x Int)) Int
              (* x 2))
            (declare-const a Int)
            (assert (>= a 50))
            (define-const b Int (potato a))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (exit)
            """
        )
        self.assertValue("b", self.values["a"] * 2)

    def test_ITE(self):
        sym_a = smt.Constant(smt.BUILTIN_INTEGER, "a")
        self.script.add_statement(
            smt.Constant_Declaration(sym_a,
                                     relevant=True))
        sym_b = smt.Constant(smt.BUILTIN_STRING, "b")
        self.script.add_statement(
            smt.Constant_Declaration(sym_b,
                                     relevant=True))

        self.script.add_statement(
            smt.Assertion(
                smt.Boolean_Negation(
                    smt.Comparison("=", sym_a, smt.Integer_Literal(0)))))

        self.script.add_statement(
            smt.Assertion(
                smt.Comparison(
                    "=",
                    sym_b,
                    smt.Conditional(
                        smt.Comparison(">",
                                       sym_a,
                                       smt.Integer_Literal(0)),
                        smt.String_Literal("positive"),
                        smt.String_Literal("negative")))))

        self.assertResult(
            "sat",
            """
            (set-logic QF_SLIA)
            (set-option :produce-models true)

            (declare-const a Int)
            (declare-const b String)
            (assert (not (= a 0)))
            (assert (= b (ite (> a 0) "positive" "negative")))
            (check-sat)
            (get-value (a))
            (get-value (b))
            (exit)
            """
        )
        if self.values["a"] > 0:
            self.assertValue("b", "positive")
        else:
            self.assertValue("b", "negative")
        self.assertNotEqual(self.values["a"], 0)
