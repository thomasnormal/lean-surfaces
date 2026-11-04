"""Nested fixed-array subarray reads lower into nested destinations."""
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


class FixedArrayNestedSubarrayCopy(unittest.TestCase):
    def test_subarray_source_pairs_ordinal_nested_cells(self):
        design = lower(
            "module top; logic [7:0] source [0:1][0:3][0:1]; "
            "logic [7:0] target [4:7][9:10]; "
            "initial target = source[1]; endmodule")
        blocks = [node for node in nodes(design)
                  if node.get("fixed_array_nested_subarray_copy_lowered")]
        self.assertEqual(len(blocks), 1)
        self.assertEqual(
            [stmt["target"]["name"] for stmt in blocks[0]["stmts"]],
            ["target[4][9]", "target[4][10]", "target[5][9]", "target[5][10]",
             "target[6][9]", "target[6][10]", "target[7][9]", "target[7][10]"])
        self.assertEqual(
            [stmt["value"]["name"] for stmt in blocks[0]["stmts"]],
            ["source[1][0][0]", "source[1][0][1]", "source[1][1][0]",
             "source[1][1][1]", "source[1][2][0]", "source[1][2][1]",
             "source[1][3][0]", "source[1][3][1]"])
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_nested_subarray_same_root_overlap_stays_loud(self):
        design = lower(
            "module top; logic [7:0] value [0:0][0:1]; "
            "initial value = value[0]; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
