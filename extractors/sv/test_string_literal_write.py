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
    def test_zero_string_character_assignment_is_ignored(self):
        design = lower(
            'module top; string value; initial begin value = "hello"; '
            'value[1] = 0; $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("string_null_char_write_noop")
                            for node in nodes(design)))

    def test_nonzero_or_dynamic_string_character_writes_stay_loud(self):
        for source in (
                'module top; string value; initial value[1] = 65; endmodule',
                'module top; string value; int i; initial value[i] = 0; endmodule',
                'module top; string value; initial value <= 0; endmodule'):
            design = lower(source)
            self.assertFalse(any(node.get("string_null_char_write_noop")
                                 for node in nodes(design)))
            self.assertTrue(any(node.get("kind") in ("Unsupported", "Invalid")
                                or node.get("sv_kind") ==
                                "AssignmentExpression:target"
                                for node in nodes(design)))

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

    def test_constant_literal_replication_write_is_inert(self):
        design = lower(
            'module top; string value; initial begin '
            'value = {3{"x"}}; $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("string_literal_replication_write_noop")
                            for node in nodes(design)))

    def test_dynamic_literal_replication_write_stays_loud(self):
        design = lower(
            'module top; string value; int count; initial begin '
            'value = {count{"x"}}; end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
