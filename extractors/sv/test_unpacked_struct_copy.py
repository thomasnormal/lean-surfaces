"""Whole copies of flattened integral unpacked structs."""

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


class UnpackedStructCopy(unittest.TestCase):
    def test_integral_struct_copy_is_cellwise(self):
        design = lower(
            'typedef struct { int a; bit [3:0] b; } T; '
            'module top; T x, y; initial y = x; endmodule')
        self.assertTrue(any(node.get("unpacked_struct_copy_lowered")
                            for node in nodes(design)))

    def test_aggregate_struct_copy_stays_loud(self):
        design = lower(
            'typedef struct { int a; string b; } T; '
            'module top; T x, y; initial y = x; endmodule')
        self.assertIn("AssignmentExpression:target",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
