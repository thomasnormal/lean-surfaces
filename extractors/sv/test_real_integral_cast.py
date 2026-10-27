"""IEEE 6.12: source-pure real-to-integral casts round away from zero."""
import unittest

from test_bit_queries import lower, nodes
from test_elaborated_generate import walls


class RealIntegralCast(unittest.TestCase):
    def test_literal_cast_rounds_to_nearest(self):
        design = lower("module top; initial begin int a, b; "
                       "a = int'(3.9); b = int'(-3.1); end endmodule")
        self.assertFalse(walls(design))
        values = [node for node in nodes(design)
                  if node.get("real_integral_cast")]
        self.assertEqual([value["bits"] for value in values], [
            "00000000000000000000000000000100",
            "11111111111111111111111111111101",
        ])

    def test_ties_round_away_from_zero(self):
        design = lower("module top; initial begin int a, b; "
                       "a = int'(2.5); b = int'(-2.5); end endmodule")
        self.assertFalse(walls(design))
        values = [node for node in nodes(design)
                  if node.get("real_integral_cast")]
        self.assertEqual([value["bits"][-4:] for value in values], ["0011", "1101"])

    def test_named_literal_history_is_source_ordered(self):
        design = lower("module top; real value; int result; initial begin "
                       "value = -3.1; result = int'(value); end endmodule")
        self.assertFalse(walls(design))

    def test_computed_or_controlled_history_stays_loud(self):
        for source in (
                "module top; real value; int result; initial begin "
                "value = 1.0 + 2.0; result = int'(value); end endmodule",
                "module top; real value; int result; initial begin "
                "if (1) value = 3.9; result = int'(value); end endmodule",
                "module top; real value; int result; initial begin "
                "#1 value = 3.9; result = int'(value); end endmodule"):
            self.assertIn("ConversionExpression:Explicit", walls(lower(source)))


if __name__ == "__main__":
    unittest.main()
