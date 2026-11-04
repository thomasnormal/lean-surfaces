"""Adapter admission for local two-state integral declarations."""
import unittest

import census
import extract
from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree


def blockers(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    extract._SOURCE_BYTES = source.encode()
    census.extract = extract
    return census.adapter_design_blockers(tree.sourceManager, compilation)


class LocalTwoStateDeclaration(unittest.TestCase):
    def test_scalar_and_packed_two_state_locals_are_admitted(self):
        self.assertEqual(
            blockers(
                'module top; initial begin '
                "bit flag = 1'bx; bit [3:0] nibble = 4'b1x0z; "
                '$display("PASS"); end endmodule'),
            [])

    def test_effectful_two_state_initializer_remains_loud(self):
        residual = blockers(
            'module top; initial begin bit [3:0] value = make_value(); '
            '$display("PASS"); end endmodule')
        self.assertIn("InvalidExpression", residual)


if __name__ == "__main__":
    unittest.main()
