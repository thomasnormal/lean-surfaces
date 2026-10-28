"""Discarded $typename calls never evaluate their argument."""

import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def extract_source(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    compilation.getAllDiagnostics()
    extract._SOURCE_BYTES = source.encode()
    return extract.convert_design(tree.sourceManager, compilation)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


class TypenameStatement(unittest.TestCase):
    def test_pure_type_name_assignment_replays_string_history(self):
        design = extract_source(
            'module top; string s; initial begin '
            's = $typename(int); if (s == "int") $display("PASS"); '
            'end endmodule')
        statements = list(nodes(design))
        self.assertIn(True, [node.get("string_source_write_noop")
                             for node in statements])
        self.assertNotIn("AssignmentExpression:target",
                         [node.get("sv_kind") for node in statements])

    def test_type_name_assignment_supports_length_query(self):
        design = extract_source(
            'module top; string s; initial begin '
            's = $typename(int); if (s.len() == 3) $display("PASS"); '
            'end endmodule')
        self.assertNotIn("CallExpression",
                         [node.get("sv_kind") for node in nodes(design)])

    def test_expression_type_name_assignment_stays_loud(self):
        design = extract_source(
            'module top; string s; int counter; initial begin '
            's = $typename(counter++); end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_side_effecting_argument_is_not_evaluated(self):
        design = extract_source(
            "module top; int counter; initial begin "
            "$typename(counter++); end endmodule")
        statements = list(nodes(design))
        self.assertIn(True, [node.get("typename_statement")
                             for node in statements])
        self.assertNotIn("ExpressionStatement:CallExpression",
                         [node.get("sv_kind") for node in statements])

    def test_missing_argument_stays_loud(self):
        design = extract_source(
            "module top; initial $typename(); endmodule")
        self.assertIn("InvalidStatement",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
