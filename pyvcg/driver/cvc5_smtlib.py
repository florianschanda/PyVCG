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

import subprocess

from fractions import Fraction

from pyvcg import smt
from pyvcg.driver.file_smtlib import SMTLIB_Generator


class Parse_Error(Exception):
    pass


class CVC5_Result_Token:
    def __init__(self, kind, value):
        self.kind  = kind
        self.value = value


class CVC5_Result_Lexer:
    def __init__(self, content):
        assert isinstance(content, str)
        self.content = content
        self.length  = len(content)
        self.lexpos  = -3
        self.line_no = 0
        self.col_no  = 0
        self.cc      = None
        self.nc      = None
        self.nnc     = None
        self.advance()
        self.advance()

    def skip_whitespace(self):
        while self.nc and self.nc.isspace():
            self.advance()
        self.advance()

    def advance(self):
        self.lexpos += 1
        if self.cc == "\n" or self.lexpos == 0:
            self.line_no += 1
            self.col_no = 0
        if self.nc is not None:
            self.col_no += 1
        self.cc = self.nc
        self.nc = self.nnc
        self.nnc = (self.content[self.lexpos + 2]
                    if self.lexpos + 2 < self.length
                    else None)

    @staticmethod
    def is_alpha(char):
        assert isinstance(char, str) and len(char) == 1
        return ord('a') <= ord(char) <= ord('z') or \
            ord('A') <= ord(char) <= ord('Z')

    @staticmethod
    def is_numeric(char):
        assert isinstance(char, str) and len(char) == 1
        return ord('0') <= ord(char) <= ord('9')

    @staticmethod
    def is_alnum(char):
        assert isinstance(char, str) and len(char) == 1
        return ord('a') <= ord(char) <= ord('z') or \
            ord('A') <= ord(char) <= ord('Z') or \
            ord('0') <= ord(char) <= ord('9')

    def token(self):
        self.skip_whitespace()
        if self.cc is None:
            return None

        start_pos  = self.lexpos

        if self.cc == "(":
            kind = "BRA"

        elif self.cc == ")":
            kind = "KET"

        elif self.is_alpha(self.cc) or self.cc == "_":
            kind = "IDENTIFIER"
            while self.nc and (self.is_alnum(self.nc) or
                               self.nc in ("_", ".", "+")):
                self.advance()

        elif self.cc == "|":
            kind = "IDENTIFIER"
            while self.nc and self.nc != "|":
                self.advance()
            self.advance()

        elif self.is_numeric(self.cc):
            kind = "NUMBER"
            while self.nc and self.is_numeric(self.nc):
                self.advance()
            if self.nc == ".":
                self.advance()
                while self.nc and self.is_numeric(self.nc):
                    self.advance()

        elif self.cc in ("-", "/"):
            kind = "OP"

        elif self.cc == "<":
            kind = "TRIANGLE_EXPR"
            while self.nc and self.nc != ">":
                self.advance()
            self.advance()

        elif self.cc == '"':
            kind = "STRING"
            while self.nc != '"':
                self.advance()
            self.advance()

        else:  # pragma: no cover
            raise Parse_Error("lex error at %s in [%s]" %
                              (self.cc, self.content))

        text = self.content[start_pos:self.lexpos + 1]

        if kind == "IDENTIFIER":
            if text.startswith("|"):
                value = text[1:-1]
            else:
                value = text
        elif kind == "NUMBER":
            if "." in text:
                value = Fraction(text)
            else:
                value = int(text)

        elif kind == "STRING":
            value = text[1:-1]

        elif kind == "OP":
            value = text

        else:
            value = None

        return CVC5_Result_Token(kind, value)


class CVC5_Result_Parser:
    def __init__(self, content):
        assert isinstance(content, str)
        self.lexer = CVC5_Result_Lexer(content)

        self.ct = None
        self.nt = None
        self.advance()

    def advance(self):
        self.ct = self.nt
        self.nt = self.lexer.token()

    def peek(self, kind):
        return self.nt is not None and self.nt.kind == kind

    def match(self, kind, value=None):
        if self.nt is None:  # pragma: no cover
            self.error("expected %s, encountered EOS instead" %
                       kind)
        if self.nt.kind != kind:  # pragma: no cover
            self.error("expected %s, encountered %s instead" %
                       (kind, self.nt.kind))
        if value is not None and self.nt.value != value:  # pragma: no cover
            self.error("expected %s, encountered %s instead" %
                       (value, self.nt.value))
        self.advance()

    def match_eos(self):
        if self.nt is not None:  # pragma: no cover
            raise Parse_Error("expected EOS, encountered %s instead" %
                              self.nt.kind)

    def parse_part1(self):
        self.match("BRA")
        self.match("BRA")
        self.match("IDENTIFIER")
        ident = self.ct.value
        return ident

    def parse_part2(self, typ):
        value = self.parse_value(typ)
        self.match("KET")
        self.match("KET")
        self.match_eos()
        return value

    def error(self, msg):  # pragma: no cover
        raise Parse_Error(msg + " in %s" % self.lexer.content)

    def parse_value(self, typ):
        assert isinstance(typ, smt.Sort)

        if typ.__class__ is smt.Sort:
            if typ.name == "Int":
                return self.parse_int()
            elif typ.name == "Real":
                return self.parse_real()
            elif typ.name == "Bool":
                return self.parse_bool()
            elif typ.name == "String":
                return self.parse_string()
            else:  # pragma: no cover
                raise Parse_Error("unexpected sort %s" % typ.name)

        elif isinstance(typ, smt.Sequence_Sort):
            return self.parse_seq(typ.element_sort())

        elif isinstance(typ, smt.Enumeration):
            return self.parse_enum()

        elif isinstance(typ, smt.Record):
            return self.parse_record(typ)

        else:  # pragma: no cover
            raise Parse_Error("unexpected sort class %s" %
                              typ.__class__.__name__)

    def parse_int(self):
        if self.peek("BRA"):
            self.match("BRA")
            self.match("OP")
            if self.ct.value == "-":
                rv = - self.parse_int()
            else:  # pragma: no cover
                self.error("unexpected int op %s" % self.ct.value)
            self.match("KET")

        else:
            self.match("NUMBER")
            rv = self.ct.value

        return rv

    def parse_real(self):
        if self.peek("BRA"):
            self.match("BRA")
            if self.peek("OP"):
                self.match("OP")
                if self.ct.value == "-":
                    rv = self.parse_real()
                    if rv is not None:  # pragma: no cover
                        # Excessive caution
                        rv = -rv
                elif self.ct.value == "/":
                    num = self.parse_real()
                    den = self.parse_real()
                    if num is None or den is None:  # pragma: no cover
                        # Excessive caution
                        rv = None
                    else:
                        rv = num / den
                else:  # pragma: no cover
                    self.error("unexpected real op %s" % self.ct.value)
            else:
                self.match("IDENTIFIER", "_")
                self.match("IDENTIFIER", "real_algebraic_number")
                self.match("TRIANGLE_EXPR")
                rv = None

            self.match("KET")

        else:
            self.match("NUMBER")
            rv = Fraction(self.ct.value)

        return rv

    def parse_bool(self):
        self.match("IDENTIFIER")
        if self.ct.value == "true":
            return True
        elif self.ct.value == "false":
            return False
        else:  # pragma: no cover
            self.error("unexpected bool value %s" % self.ct.value)

    def parse_string(self):
        self.match("STRING")
        return self.ct.value

    def parse_seq(self, etyp):
        assert isinstance(etyp, smt.Sort)
        self.match("BRA")
        self.match("IDENTIFIER")
        if self.ct.value == "seq.++":
            rv = []
            while self.nt and not self.peek("KET"):
                rv += self.parse_seq(etyp)
        elif self.ct.value == "seq.unit":
            rv = [self.parse_value(etyp)]
        elif self.ct.value == "as":
            self.match("IDENTIFIER", "seq.empty")
            self.match("BRA")
            while self.nt and not self.peek("KET"):
                self.advance()
            self.match("KET")
            rv = []
        else:  # pragma: no cover
            self.error("unexpected seq op %s" % self.ct.value)
        self.match("KET")
        return rv

    def parse_enum(self):
        self.match("IDENTIFIER")
        return self.ct.value

    def parse_record(self, typ):
        assert isinstance(typ, smt.Record)
        self.match("BRA")
        self.match("IDENTIFIER")
        if typ.name + "__cons" != self.ct.value:  # pragma: no cover
            self.error("unexpected constructor %s (expected %s)" %
                       (self.ct.value,
                        typ.name + "__cons"))
        rv = {}
        for name, sort in typ.components.items():
            rv[name] = self.parse_value(sort)
        self.match("KET")
        return rv


class CVC5_File_Solver(SMTLIB_Generator, smt.VC_Solver):
    def __init__(self, cvc5_binary=None):
        SMTLIB_Generator.__init__(self)
        smt.VC_Solver.__init__(self)
        self.binary          = cvc5_binary if cvc5_binary else "cvc5"
        self.instance        = None
        self.result          = None
        self.model           = {}
        self.relevant_values = {}
        self.records         = {}

    def visit_script(self, node, logic, functions):
        self.instance = super().visit_script(node, logic, functions)

    def visit_constant_declaration(self, node, tr_symbol, tr_value):
        super().visit_constant_declaration(node, tr_symbol, tr_value)
        if node.is_relevant:
            self.relevant_values[node.symbol.name] = node.symbol

    def visit_record_declaration(self, node):
        super().visit_record_declaration(node)
        self.records[node.sort.name] = node.sort

    def solve(self):
        result = subprocess.run([self.binary,
                                 "--lang=smt2",
                                 "-"],
                                input          = self.instance,
                                capture_output = True,
                                check          = True,
                                encoding       = "UTF-8")
        lines = result.stdout.splitlines()
        status, tail = lines[0].strip(), lines[1:]
        assert status in ("sat", "unsat", "unknown"), \
            "invalid status %s" % status
        self.result = status
        if self.result == "unsat":
            return

        for raw_line in tail:
            parser = CVC5_Result_Parser(raw_line)
            ident = parser.parse_part1()
            value = parser.parse_part2(self.relevant_values[ident].sort)
            self.model[ident] = value

    def get_status(self):
        assert self.result is not None
        return self.result

    def get_values(self):
        assert self.result is not None
        return self.model
