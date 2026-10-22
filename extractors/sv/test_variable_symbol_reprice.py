"""Shape checks for VariableSymbol repricing."""
import unittest

from variable_symbol_reprice import variable_features


class VariableSymbolReprice(unittest.TestCase):
    def test_compilation_unit_scope(self):
        self.assertEqual(
            variable_features("int unit_global = 42; module top; endmodule",
                              "unit_global = 42"),
            ("compilation-unit-variable",))

    def test_unit_scope_and_multiple_top_levels(self):
        self.assertEqual(
            variable_features("int peer_seen; module a; endmodule "
                              "module b; endmodule", "peer_seen"),
            ("compilation-unit-variable", "multiple-top-level-modules"))

    def test_enum_range_and_invalid_int_dimension(self):
        self.assertEqual(
            variable_features("enum { register[2] = 1 } vr; module top; "
                              "endmodule", "vr"),
            ("enum-range-declaration",))
        self.assertEqual(
            variable_features("int [3:0] bad_packed_int; module top; "
                              "endmodule", "bad_packed_int"),
            ("invalid-packed-dimension-on-int", "compilation-unit-variable"))


if __name__ == "__main__":
    unittest.main()
