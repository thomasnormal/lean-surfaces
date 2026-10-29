"""The adapter follows the extractor's exact integral-parameter path."""

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


class ParameterAdapter(unittest.TestCase):
    def test_exact_integral_parameters_are_metadata(self):
        self.assertEqual(
            blockers(
                'module top #(parameter int W=8, parameter logic [3:0] M=4\'ha); '
                'logic [W-1:0] value=8\'hA5; '
                'initial $display("%0d %0h %0h", W, M, value); endmodule'),
            [])

    def test_non_integral_parameters_remain_loud(self):
        self.assertIn(
            "ParameterSymbol:Parameter",
            blockers('module top #(parameter real R=1.5); '
                     'initial $display("PASS"); endmodule'))

    def test_compilation_unit_integral_parameter_is_metadata(self):
        self.assertEqual(
            blockers('parameter int U=8; module top; '
                     'initial $display("%0d", U); endmodule'),
            [])


if __name__ == "__main__":
    unittest.main()
