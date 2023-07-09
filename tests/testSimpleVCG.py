import unittest
import shutil
import glob
import os

from io import StringIO
from fractions import Fraction

from pyvcg import smt
from pyvcg import graph
from pyvcg import vcg
from pyvcg.driver.file_smtlib import SMTLIB_Generator
from pyvcg.driver.cvc5_api import CVC5_Solver


class SimpleVCG(unittest.TestCase):
    def setUp(self):
        self.vcg   = vcg.VCG()
        self.graph = self.vcg.graph

    def writeExpectedOutput(self, basename):
        assert isinstance(basename, str)

        self.vcg.generate()

        for filename in glob.glob("tests/SimpleVCG_Output/%s_*.smt2"):
            os.system("git rm %s" % filename)

        filename = "tests/SimpleVCG_Output/%s.dot" % basename
        with open(filename, "w", encoding="UTF-8") as fd:
            fd.write(self.graph.debug_render_dot())
            fd.write("\n")
        os.system("git add %s" % filename)
        os.system("dot -Tpdf %s -o %s" % (filename,
                                          filename.replace(".dot",
                                                           ".pdf")))

        for vc_id, vc in enumerate(self.vcg.vcs, 1):
            filename = "tests/SimpleVCG_Output/%s_%04u.smt2" % (basename,
                                                                vc_id)
            with open(filename,
                      "w",
                      encoding="UTF-8") as fd:
                fd.write(vc["script"].generate_vc(SMTLIB_Generator()))
                fd.write("\n")
                status, values = vc["script"].solve_vc(CVC5_Solver())
                fd.write(";; result = %s\n" % status)
                if values:
                    fd.write(";;\n")
                for name, value in values.items():
                    fd.write(";; %s = %s\n" % (name, value))
            os.system("git add %s" % filename)

    def test_trivial_flat(self):
        n1 = graph.Assumption(self.graph)
        self.graph.start.add_edge_to(n1)

        potato = smt.Constant(smt.BUILTIN_BOOLEAN, "potato")
        n1.add_statement(smt.Constant_Declaration(potato, relevant=True))

        n2 = graph.Check(self.graph)
        n1.add_edge_to(n2)

        n2.add_goal(potato, comment = "first attempt")
        n2.add_goal(potato, comment = "second attempt")

        self.writeExpectedOutput("trivial_flat")

    def test_trivial_paths(self):
        n1 = graph.Assumption(self.graph)
        myvar = smt.Constant(smt.BUILTIN_INTEGER, "x")
        n1.add_statement(smt.Constant_Declaration(myvar, relevant=True))
        self.graph.start.add_edge_to(n1)

        n2 = graph.Assumption(self.graph)
        n2.add_statement(smt.Assertion(smt.Comparison(">",
                                                      myvar,
                                                      smt.Integer_Literal(5))))
        n1.add_edge_to(n2)

        n3 = graph.Assumption(self.graph)
        n3.add_statement(smt.Assertion(smt.Comparison(">",
                                                      myvar,
                                                      smt.Integer_Literal(1))))
        n1.add_edge_to(n3)

        n4 = graph.Check(self.graph)
        n4.add_goal(
            smt.Boolean_Negation(
                smt.Comparison("=",
                               myvar,
                               smt.Integer_Literal(0))))
        n4.add_goal(
            smt.Boolean_Negation(
                smt.Comparison("=",
                               myvar,
                               smt.Integer_Literal(3))))
        n2.add_edge_to(n4)
        n3.add_edge_to(n4)

        self.writeExpectedOutput("trivial_paths")
