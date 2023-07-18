import unittest

from pyvcg.driver.file_smtlib import SMTLIB_Generator


class StringTests(unittest.TestCase):
    def setUp(self):
        self.driver = SMTLIB_Generator()

    def testStringEscaping(self):
        s = self.driver.escape_string_literal('"pot\nato"')
        self.assertEqual(s, r'""pot\u{a}ato""')
