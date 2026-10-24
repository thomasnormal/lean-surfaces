"""Literal-only string concatenation writes are inert at self-check time 0."""

import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def lower(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
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


class LiteralStringWrites(unittest.TestCase):
    def test_literal_concatenation_write_is_inert(self):
        design = lower(
            'module top; string value; initial begin '
            'value = {"left", "-", "right"}; $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("string_literal_concat_write_noop")
                            for node in nodes(design)))

    def test_dynamic_concatenation_write_stays_loud(self):
        design = lower(
            'module top; string value; string source; initial begin '
            'value = {source, "right"}; end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_nonblocking_literal_concatenation_stays_loud(self):
        design = lower(
            'module top; string value; initial begin '
            'value <= {"left", "right"}; end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
