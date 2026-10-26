"""One dynamic index through a finite multidimensional array lowers cellwise."""
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


class NestedFixedArrayDynamicTarget(unittest.TestCase):
    def test_one_dynamic_dimension_lowers(self):
        design = lower(
            'module top; int value [0:1][0:1]; integer index; '
            'initial begin value[0][1] = 7; value[1][1] = 8; index = 1; '
            'if (value[1][index] === 8) $display("PASS"); end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))
        self.assertGreaterEqual(sum(node.get("kind") == "If" for node in nodes(design)), 1)

    def test_two_dynamic_dimensions_stay_loud(self):
        design = lower(
            'module top; int value [0:1][0:1]; integer i, j; '
            'initial begin i = 0; j = 1; value[i][j] = 8; end endmodule')
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "AssignmentExpression:target"
                            for node in nodes(design)))

    def test_one_dynamic_outer_dimension_also_lowers(self):
        design = lower(
            'module top; int value [0:1][0:1]; integer index; '
            'initial begin value[0][1] = 7; value[1][1] = 8; index = 1; '
            'value[index][1] = 9; if (value[1][1] === 9) $display("PASS"); '
            'end endmodule')
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
