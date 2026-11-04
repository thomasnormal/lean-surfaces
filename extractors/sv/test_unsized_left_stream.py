"""Unsized left streams use the IEEE one-bit default for one-bit leaves."""
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


class UnsizedLeftStream(unittest.TestCase):
    def test_one_bit_leaves_use_default_chunk(self):
        design = lower(
            "module top; bit a, b, c, d; initial begin "
            "{<< {a, b, c, d}} = 4'b1010; "
            "if ({a, b, c, d} === 4'b0101) $display(\"PASS\"); "
            "end endmodule")
        assigns = [node for node in nodes(design)
                   if node.get("kind") == "BlockingAssign"]
        self.assertEqual(len(assigns), 1)
        self.assertEqual(assigns[0]["target"]["width"], 4)
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_wider_unsized_leaves_stay_loud(self):
        design = lower(
            "module top; bit [3:0] hi, lo; "
            "initial {<< {hi, lo}} = 8'b10101010; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
