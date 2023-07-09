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

import html

from pyvcg import smt
from pyvcg.driver.file_smtlib import SMTLIB_Generator


class DAG:
    def __init__(self):
        self.node_id = -1
        self.nodes = []
        self.start = None

    def debug_render_dot(self):
        dot = ["digraph {"]
        for node in self.nodes:
            writer = SMTLIB_Generator()
            if isinstance(node, Check):
                for check in node.goals:
                    if check["comment"]:
                        writer.lines.append(";; %s" % check["comment"])
                    writer.lines.append("goal: %s" %
                                        check["goal"].walk(writer))
            else:
                for item in node.items:
                    item.walk(writer)

            label = "<b>%s</b><br/>" % node.__class__.__name__
            label += "<br/>".join(map(html.escape, writer.lines))

            dot.append("  %u [label=<%s>]" % (node.node_id, label))
        for node_src in self.nodes:
            for node_dst in node_src.outgoing:
                dot.append("  %u -> %u" % (node_src.node_id,
                                           node_dst.node_id))
        dot.append("}")
        return "\n".join(dot)

    def register_node(self, node):
        assert isinstance(node, Node)
        self.node_id += 1
        node.node_id = self.node_id
        self.nodes.append(node)
        if isinstance(node, Start):
            assert self.start is None
            self.start = node

    def path_exists(self, n_from, n_to):
        assert isinstance(n_from, Node)
        assert isinstance(n_to, Node)
        assert n_from.graph is n_to.graph

        worklist = [n_from]
        while worklist:
            n_ptr = worklist.pop()
            if n_ptr is n_to:
                return True
            worklist += n_ptr.outgoing

        return False

    def all_paths_to_checks(self, start=None):
        assert isinstance(start, Node) or start is None
        if start is None:
            start = self.start

        for node in start.outgoing:
            for sub_path in self.all_paths_to_checks(node):
                yield [start.node_id] + sub_path

        if isinstance(start, Check):
            yield [start.node_id]

    def all_mapped_paths_to_checks(self):
        for path in self.all_paths_to_checks():
            yield [self.nodes[node_id] for node_id in path]


class Node:
    def __init__(self, graph):
        assert isinstance(graph, DAG)

        self.graph    = graph
        self.node_id  = None
        self.outgoing = []
        self.incoming = []
        self.items    = []

        self.graph.register_node(self)

    def add_edge_to(self, other):
        assert isinstance(other, Node)
        assert other.graph is self.graph
        assert not self.graph.path_exists(other, self), \
            "adding this edge forms a cycle"

        self.outgoing.append(other)
        other.incoming.append(self)

    def add_statement(self, statement):
        assert isinstance(statement, smt.Statement)
        self.items.append(statement)


class Start(Node):
    # Special "program start" node
    def __init__(self, graph):  # pylint: disable=useless-parent-delegation
        super().__init__(graph)


class Assumption(Node):
    # Assumptions insert knowledge and declarations
    def __init__(self, graph):  # pylint: disable=useless-parent-delegation
        super().__init__(graph)


class Check(Node):
    # Emit a VC for the given goal, contributes knowledge on outgoing
    # nodes
    def __init__(self, graph):  # pylint: disable=useless-parent-delegation
        super().__init__(graph)
        self.goals = []

    def add_statement(self, statement):
        assert False

    def add_goal(self, expression, feedback=None, comment=None):
        assert isinstance(expression, smt.Expression)
        assert isinstance(comment, str) or comment is None
        assert expression.sort is smt.BUILTIN_BOOLEAN
        self.goals.append({"goal"     : expression,
                           "feedback" : feedback,
                           "comment"  : comment})
        self.items.append(smt.Assertion(expression))


class Sequential_Choices(Node):  # pragma: no cover
    # Models an if... elseif... elseif... else... construct. The
    # semantics are that each path is evaluated in turn until we find
    # one that matches.
    #
    # In other words, for something like if a... elseif b... else... we
    # generate:
    # * a -> stuff
    # * not a /\ b -> stuff
    # * not a /\ not b -> stuff
    def __init__(self, graph):  # pylint: disable=useless-parent-delegation
        super().__init__(graph)
