"""Pure all-literal integral net drivers fold at time zero."""
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


class ConstantExpressionNetDriver(unittest.TestCase):
    def test_unsigned_literal_expression_driver_lowers(self):
        design = lower(
            'module top; wire [3:0] driven; '
            "assign driven = 4'd3 * 4'd2; "
            'initial if (driven === 4\'d6) $display("PASS"); endmodule')
        lowered = [node for node in nodes(design)
                   if node.get("continuous_constant_lowered")]
        self.assertGreaterEqual(len(lowered), 1)
        driver = next(node for node in lowered if node.get("body", {}).get("kind") == "BlockingAssign")
        self.assertEqual(driver["body"]["value"]["bits"], "0110")
        self.assertFalse(any(node.get("sv_kind") == "AssignmentExpression:target"
                             for node in nodes(design)))

    def test_variable_expression_driver_stays_live(self):
        design = lower(
            'module top; logic source; wire [3:0] driven; '
            'assign driven = source + 4\'d1; endmodule')
        self.assertTrue(any(node.get("kind") == "Assign"
                            for node in nodes(design)))
        self.assertFalse(any(node.get("continuous_constant_lowered")
                             for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
