"""Shape checks for delay-expression repricing."""

import unittest

from delay_expression_reprice import delay_expression_features


class DelayExpressionReprice(unittest.TestCase):
    def test_dynamic_parameter_arithmetic(self):
        self.assertEqual(
            delay_expression_features(
                "#((d+e)/2);",
                "module top; parameter d = 20; parameter e = 40; endmodule",
                "/tests/chapter-9/9.4.1--delay-expression-averaging-v4.sv",
            ),
            ("delay-expression", "dynamic-reference", "arithmetic-expression",
             "parameter-or-signal"),
        )

    def test_unit_and_precision(self):
        self.assertEqual(
            delay_expression_features(
                "#1.2ns;",
                "`timescale 1ns/100ps\ntimeprecision 100ps; #1.2ns;",
                "/tests/chapter-3/3.14.2.3--timescale.sv",
            ),
            ("delay-expression", "unit-suffixed", "fixed-point",
             "time-scale-precision"),
        )

    def test_unknown_zero_and_delayed_assignment(self):
        self.assertEqual(
            delay_expression_features(
                "#d x_val = 1;",
                "description: delay x or z value treated as zero\n",
                "/tests/chapter-9/9.4.1--delay-x-or-z-value-treated-as-zero.sv",
            ),
            ("delay-expression", "dynamic-reference", "x-z-zero",
             "delay-before-assignment", "parameter-or-signal"),
        )


if __name__ == "__main__":
    unittest.main()
