"""Nested fixed-array conditional assignments lower cellwise."""
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


class FixedArrayNestedConditional(unittest.TestCase):
    def test_nested_conditional_pairs_ordinal_cells(self):
        design = lower(
            "module top; logic [7:0] source [0:1][0:1]; "
            "logic [7:0] value [4:5][9:8]; logic choose; "
            "initial begin value = choose ? value : source; end endmodule")
        blocks = [node for node in nodes(design)
                  if node.get("fixed_array_nested_conditional_lowered")]
        self.assertEqual(len(blocks), 1)
        self.assertEqual(
            [stmt["target"]["name"] for stmt in blocks[0]["stmts"]],
            ["value[4][9]", "value[4][8]", "value[5][9]", "value[5][8]"])
        self.assertEqual(
            [stmt["value"]["then"]["name"] for stmt in blocks[0]["stmts"]],
            ["value[4][9]", "value[4][8]", "value[5][9]", "value[5][8]"])
        self.assertEqual(
            [stmt["value"]["else"]["name"] for stmt in blocks[0]["stmts"]],
            ["source[0][0]", "source[0][1]", "source[1][0]", "source[1][1]"])
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_nested_nonblocking_self_alias_stays_loud(self):
        design = lower(
            "module top; logic [7:0] source [0:1][0:1]; "
            "logic [7:0] value [0:1][0:1]; logic choose; "
            "initial value <= choose ? value : source; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") ==
                            "AssignmentExpression:target"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
