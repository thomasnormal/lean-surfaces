"""Whole fixed-unpacked copies accept a wire-array source."""
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


class FixedArrayNetCopy(unittest.TestCase):
    def test_wire_array_source_copies_cells(self):
        design = lower(
            'module top; logic [7:0] value [0:1]; '
            'wire [7:0] source [0:1]; '
            'assign source[0] = 8\'h12; assign source[1] = 8\'h34; '
            'initial begin value = source; '
            'if (value[0] === 8\'h12 && value[1] === 8\'h34) '
            '$display("PASS"); end endmodule')
        blocks = [node for node in nodes(design)
                  if node.get("kind") == "Block"
                  and node.get("fixed_array_net_copy_lowered")]
        self.assertEqual(len(blocks), 1)
        self.assertEqual([stmt["target"]["name"] for stmt in blocks[0]["stmts"]],
                         ["value[0]", "value[1]"])
        self.assertEqual([stmt["value"]["name"] for stmt in blocks[0]["stmts"]],
                         ["source[0]", "source[1]"])
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_dynamic_or_mismatched_source_stays_loud(self):
        design = lower(
            'module top; logic [7:0] value [0:1]; '
            'wire [7:0] source [0:2]; initial value = source; endmodule')
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
