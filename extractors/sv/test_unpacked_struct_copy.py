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

    def test_positional_struct_pattern_is_fieldwise(self):
        design = lower(
            "typedef struct { bit [3:0] a; logic [3:0] b; } T; "
            "module top; T x; initial x = '{4'b1x01, 4'b0101}; endmodule")
        lowered = [node for node in nodes(design)
                   if node.get("unpacked_struct_pattern_lowered")]
        self.assertEqual(len(lowered), 1)
        stmts = lowered[0]["stmts"]
        self.assertEqual([stmt["target"]["name"] for stmt in stmts],
                         ["x.a", "x.b"])
        self.assertEqual(stmts[0]["value"]["kind"], "Squash2")
        self.assertEqual(stmts[0]["value"]["operand"]["bits"], "1x01")
        self.assertEqual(stmts[1]["value"]["bits"], "0101")


if __name__ == "__main__":
    unittest.main()
