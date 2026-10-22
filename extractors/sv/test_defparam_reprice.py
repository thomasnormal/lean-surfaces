"""Shape checks for defparam repricing."""

import unittest

from defparam_reprice import defparam_features


class DefParamReprice(unittest.TestCase):
    def test_deep_array_and_parameter_rhs(self):
        self.assertEqual(
            defparam_features(
                "top.arr[1].submod.ID = BASE + 3;",
                "module top; parameter BASE = 1; defparam top.arr[1].submod.ID = BASE + 3; endmodule",
            ),
            ("hierarchical-target", "deep-path", "array-element",
             "rhs-parameter", "rhs-arithmetic"),
        )

    def test_multi_and_last_wins(self):
        source = """
module top;
  defparam u.A = 1, u.B = 2;
  defparam u.A = 3;
endmodule
"""
        self.assertEqual(
            defparam_features("u.A = 1;", source),
            ("hierarchical-target", "last-wins", "multi-params"),
        )

    def test_precedence_diagnostic_and_type(self):
        source = """
:type: compile_error
:description: defparam wins over instance parameter and cannot target an array
module top;
  defparam top.arr[1].P = 2;
endmodule
"""
        self.assertEqual(
            defparam_features("top.arr[1].P = 2;", source,
                              "/tests/chapter-37/37.2--defparam-type.sv"),
            ("hierarchical-target", "deep-path", "array-element",
             "instance-precedence", "diagnostic", "type-example"),
        )


if __name__ == "__main__":
    unittest.main()
