"""Zero-size queries on untouched queue and dynamic-array declarations."""

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


class SizeQueries(unittest.TestCase):
    def test_uninitialized_queue_size_is_zero(self):
        design = lower(
            'module top; int q[$]; initial $display("%0d", q.size()); endmodule')
        values = [node for node in nodes(design)
                  if node.get("zero_size_query")]
        self.assertEqual([(node["width"], node["bits"]) for node in values],
                         [(32, "0" * 32)])

    def test_uninitialized_dynamic_array_size_is_zero(self):
        design = lower(
            'module top; int values[]; initial $display("%0d", values.size()); endmodule')
        self.assertTrue(any(node.get("zero_size_query") for node in nodes(design)))

    def test_mutated_queue_size_stays_loud(self):
        design = lower(
            'module top; int q[$]; initial begin q.push_back(1); '
            '$display("%0d", q.size()); end endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_initialized_queue_size_stays_loud(self):
        design = lower(
            'module top; int q[$] = {1}; initial $display("%0d", q.size()); endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_uninitialized_string_len_is_zero(self):
        design = lower(
            'module top; string s; initial $display("%0d", s.len()); endmodule')
        self.assertTrue(any(node.get("zero_string_length_query")
                            for node in nodes(design)))

    def test_written_string_len_stays_loud(self):
        design = lower(
            'module top; string s; initial begin s = "x"; '
            '$display("%0d", s.len()); end endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_empty_queue_write_keeps_size_zero(self):
        design = lower(
            'module top; int q[$]; initial begin q = {}; '
            '$display("%0d", q.size()); end endmodule')
        self.assertTrue(any(node.get("zero_size_query") for node in nodes(design)))

    def test_empty_string_write_keeps_len_zero(self):
        design = lower(
            'module top; string s; initial begin s = ""; '
            '$display("%0d", s.len()); end endmodule')
        self.assertTrue(any(node.get("zero_string_length_query")
                            for node in nodes(design)))

    def test_nonempty_write_before_query_stays_loud(self):
        design = lower(
            'module top; int q[$]; initial begin q = {}; q.push_back(1); '
            '$display("%0d", q.size()); end endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))

    def test_zero_dynamic_allocation_keeps_size_zero(self):
        design = lower(
            'module top; int values[]; initial begin values = new[0]; '
            '$display("%0d", values.size()); end endmodule')
        self.assertTrue(any(node.get("zero_size_query") for node in nodes(design)))

    def test_positive_dynamic_allocation_size_stays_loud(self):
        design = lower(
            'module top; int values[]; initial begin values = new[1]; '
            '$display("%0d", values.size()); end endmodule')
        self.assertTrue(any(node.get("sv_kind") == "CallExpression"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
