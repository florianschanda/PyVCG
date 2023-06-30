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

from io import StringIO

from pyvcg import smt
from pyvcg import graph


class VCG:
    def __init__(self):
        self.graph = graph.DAG()
        self.start = graph.Start(self.graph)
        self.vcs   = []

    def build_sub_vc(self, statements):
        vc = {
            "smtlib" : smt.SMTLIB_Context(StringIO()),
            "api"    : smt.CVC5_Context(),
        }
        for statement in statements:
            vc["smtlib"].add_statement(statement)
            vc["api"].add_statement(statement)
        vc["smtlib"].generate()
        vc["api"].generate()
        self.vcs.append(vc)

    def build_vc(self, full_path):
        path, goal_node = full_path[:-1], full_path[-1]
        assert isinstance(goal_node, graph.Check)

        proved_goals = []
        for goal in goal_node.goals:
            # Add all knowledge from path
            statements = []
            for node in path:
                statements += node.items

            # Add previously proven goals from this check
            statements += proved_goals

            # Add goal
            statements.append(smt.Assertion(smt.Boolean_Negation(goal)))

            # Generate VC
            self.build_sub_vc(statements)

            # Add proven goal to local knowledge
            proved_goals.append(smt.Assertion(goal))

    def generate(self):
        for path in self.graph.all_mapped_paths_to_checks():
            self.build_vc(path)
