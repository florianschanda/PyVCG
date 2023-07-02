import unittest
import shutil
import glob
import os

from io import StringIO
from fractions import Fraction

from pyvcg import smt
from pyvcg import graph
from pyvcg import vcg


class SimpleVCG(unittest.TestCase):
    def setUp(self):
        self.vcg   = vcg.VCG()
        self.graph = self.vcg.graph

    def writeExpectedOutput(self, basename):
        assert isinstance(basename, str)

        self.vcg.generate()

        for filename in glob.glob("tests/SimpleVCG_Output/%s_*.smt2"):
            os.system("git rm %s" % filename)
        for vc_id, vc in enumerate(self.vcg.vcs, 1):
            filename = "tests/SimpleVCG_Output/%s_%04u.smt2" % (basename,
                                                                vc_id)
            with open(filename,
                      "w",
                      encoding="UTF-8") as fd:
                fd.write(vc.generate_vc(smt.SMTLIB_Generator()))
                fd.write("\n")
                status, values = vc.solve_vc(smt.CVC5_Solver())
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

        n2.add_goal(potato)
        n2.add_goal(potato)

        for vc in self.vcg.vcs:
            print(vc["smtlib"].fd.getvalue())

        self.writeExpectedOutput("trivial_flat")
