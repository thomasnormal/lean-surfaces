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

    def test_compilation_unit_typedef_is_metadata(self):
        self.assertEqual(
            blockers("typedef logic [7:0] byte_t; module top; "
                     "byte_t b=8'hA5; initial begin $display(\"%0h\", b); "
                     "$display(\"PASS\"); end endmodule"),
            [])

    def test_metadata_only_package_and_import_are_erased(self):
        self.assertEqual(
            blockers("package P; typedef logic [7:0] byte_t; endpackage "
                     "module top; import P::byte_t; byte_t b=8'hA5; "
                     "initial begin $display(\"%0h\", b); "
                     "$display(\"PASS\"); end endmodule"),
            [])

    def test_referenced_package_subroutine_remains_loud(self):
        residual = blockers("package P; function int f(int x); "
                            "return x+1; endfunction endpackage "
                            "module top; import P::*; "
                            "initial $display(\"%0d\", f(1)); endmodule")
        self.assertIn("PackageSymbol", residual)

    def test_bound_inside_expression_reuses_elaborated_parameters(self):
        self.assertEqual(
            blockers("module top; int a; int b=12; "
                     "localparam c=5; localparam d=7; "
                     "initial begin a = b inside {c,d}; "
                     "$display(\"%0d\", a); end endmodule"),
            [])

    def test_display_format_escape_is_not_an_expression_argument(self):
        self.assertEqual(
            blockers('module top; initial $display("octal \\123"); endmodule'),
            [])

    def test_resolved_forward_typedef_is_metadata(self):
        self.assertEqual(
            blockers("typedef int word_t; typedef word_t; module top; "
                     "word_t value=42; initial begin $display(\"%0d\", value); "
                     "$display(\"PASS\"); end endmodule"),
            [])

    def test_unresolved_forward_typedef_remains_loud(self):
        self.assertIn(
            "ForwardingTypedefSymbol",
            blockers("typedef missing_t; module top; "
                     "initial $display(\"PASS\"); endmodule"))


if __name__ == "__main__":
    unittest.main()
