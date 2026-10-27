"""Exact scalar-literal queue to fixed-array copies use flat cells."""

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


class QueueFixedArrayCopy(unittest.TestCase):
    def test_same_count_literal_queue_copies_left_to_right(self):
        design = lower(
            "module top; int dst [0:2]; int q[$] = '{10, 20, 30}; "
            "initial begin dst = q; "
            "if (dst[0] == 10 && dst[1] == 20 && dst[2] == 30) "
            "$display(\"PASS\"); end endmodule")
        blocks = [node for node in nodes(design)
                  if node.get("queue_fixed_array_copy_lowered")]
        self.assertEqual(len(blocks), 1)
        self.assertEqual([stmt["target"]["name"] for stmt in blocks[0]["stmts"]],
                         ["dst[0]", "dst[1]", "dst[2]"])
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_size_mismatch_stays_loud(self):
        design = lower(
            "module top; int dst [0:1]; int q[$] = '{10, 20, 30}; "
            "initial dst = q; endmodule")
        self.assertTrue(any(node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_later_queue_use_stays_loud(self):
        design = lower(
            "module top; int dst [0:1]; int q[$] = '{10, 20}; "
            "initial begin dst = q; $display(\"%0d\", q.size()); end endmodule")
        self.assertTrue(any(node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
