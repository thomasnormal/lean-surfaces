"""Empty queue writes are inert in the flat time-zero self-check state."""

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


class EmptyQueueWrites(unittest.TestCase):
    def test_empty_queue_write_is_inert(self):
        design = lower(
            'module top; int q[$]; initial begin q = {}; '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("empty_queue_write_noop")
                            for node in nodes(design)))

    def test_unobserved_literal_queue_write_is_inert(self):
        design = lower(
            'module top; int q[$]; initial begin q = {1, 2}; '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") ==
                             "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("queue_literal_write_noop")
                            for node in nodes(design)))

    def test_observed_literal_queue_write_stays_loud(self):
        design = lower(
            'module top; int q[$]; initial begin q = {1, 2}; '
            'if (q.size() == 2) $display("PASS"); end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_dynamic_queue_write_stays_loud(self):
        design = lower(
            'module top; int q[$]; int value; initial begin '
            'q = {value}; end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_nonblocking_empty_queue_write_stays_loud(self):
        design = lower(
            'module top; int q[$]; initial begin q <= {}; end endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_empty_dynamic_array_write_is_inert(self):
        design = lower(
            'module top; int values[]; initial begin values = {}; '
            '$display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertTrue(any(node.get("empty_dynamic_array_write_noop")
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
