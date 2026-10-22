"""Shape checks for Package:Subroutine repricing."""
import unittest

from package_subroutine_reprice import subroutine_features


class PackageSubroutineReprice(unittest.TestCase):
    def test_constant_package_function(self):
        self.assertEqual(
            subroutine_features(
                "package p; function automatic int f(int x); return x + 1; "
                "endfunction endpackage module m; localparam int n = f(2);",
                "function automatic int f(int x); return x + 1; endfunction"),
            ("package-function", "constant-function-use"))

    def test_nonconstant_package_function(self):
        self.assertEqual(
            subroutine_features(
                "package p; function string label(int x); return \"x\"; "
                "endfunction endpackage module m; initial $display(\"ok\");",
                "function string label(int x); return \"x\"; endfunction"),
            ("package-function", "nonconstant-function"))

    def test_dpi_import(self):
        self.assertEqual(
            subroutine_features(
                'package p; import "DPI-C" function int abs(input int x); '
                'endpackage',
                'import "DPI-C" function int abs(input int x);'),
            ("dpi-import",))


if __name__ == "__main__":
    unittest.main()
