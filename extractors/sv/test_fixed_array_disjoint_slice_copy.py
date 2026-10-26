"""Disjoint fixed-unpacked slice copies lower cellwise."""
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


class FixedArrayDisjointSliceCopy(unittest.TestCase):
    def test_disjoint_same_array_slices_lower(self):
        design = lower(
            'module top; int value [0:3]; initial begin '
            "value = '{1, 2, 3, 4}; value[0:1] = value[2:3]; "
            'if (value[0] === 3 && value[1] === 4) $display("PASS"); '
            'end endmodule')
        blocks = [node for node in nodes(design)
                  if node.get("fixed_array_slice_copy_lowered")]
        self.assertEqual(len(blocks), 1)
        self.assertEqual([stmt["target"]["name"] for stmt in blocks[0]["stmts"]],
                         ["value[0]", "value[1]"])
        self.assertEqual([stmt["value"]["operand"]["name"]
                          for stmt in blocks[0]["stmts"]],
                         ["value[2]", "value[3]"])
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_overlapping_same_array_slices_stay_loud(self):
        design = lower(
            'module top; int value [0:3]; '
            'initial value[1:2] = value[0:1]; endmodule')
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
