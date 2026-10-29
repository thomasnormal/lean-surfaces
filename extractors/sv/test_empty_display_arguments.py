"""Adapter and extractor handling for omitted output arguments."""
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


class EmptyDisplayArguments(unittest.TestCase):
    def test_omitted_no_format_arguments_are_supported(self):
        self.assertEqual(
            blockers('module top; initial $display(5, , 2, , 3); endmodule'),
            [])

    def test_omitted_format_operand_remains_loud(self):
        residual = blockers('module top; initial $display("%0d", , 5); endmodule')
        self.assertIn("SysCall:empty-argument-format", residual)


if __name__ == "__main__":
    unittest.main()
