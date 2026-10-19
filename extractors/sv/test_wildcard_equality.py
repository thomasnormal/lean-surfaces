"""IEEE 1800-2023 11.4.6: retain wildcard comparisons and their type boundary."""

import unittest
from pathlib import Path

from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=WildcardEquality | origin=spec | authority=IEEE-1800-2023#11.4.6 | map=nodes:retain-both-operators-with-one-bit-results-and-elaborated-operand-types


def comparisons(design):
    return [node for node in nodes(design)
            if node.get("kind") == "Binary" and node.get("op") in ("==?", "!=?")]


class WildcardEquality(unittest.TestCase):
    def test_both_operators_keep_one_bit_results(self):
        for declaration in ("logic", "logic [3:0]", "logic signed [64:0]"):
            with self.subTest(declaration=declaration):
                design = lower("module top; " + declaration + " a, b; logic x, y; "
                               "initial begin x = a ==? b; y = a !=? b; end endmodule")
                self.assertEqual([node["op"] for node in comparisons(design)], ["==?", "!=?"])
                self.assertTrue(all(node["width"] == 1 for node in comparisons(design)))
                self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_widened_result_keeps_self_determined_comparison(self):
        design = lower("module top; logic [3:0] a, b; logic [15:0] result; "
                       "initial result = a ==? b; endmodule")
        comparison = comparisons(design)[0]
        self.assertEqual(comparison["width"], 1)
        self.assertEqual([comparison[s]["width"] for s in ("left", "right")], [4, 4])

    def test_symbolic_operators_are_retained(self):
        design = symbolic("module divider #(parameter W=8) "
                          "(input logic [W-1:0] a, b, output logic x, y); "
                          "assign x = a ==? b; assign y = a !=? b; endmodule")
        self.assertEqual([node["op"] for node in comparisons(design)], ["==?", "!=?"])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_nested_comparisons_keep_operand_signedness(self):
        for operator in ("==?", "!=?"):
            design = symbolic("module divider #(parameter W=8) "
                              "(output logic [W-1:0] result); "
                              "assign result = ((-4'sh8) " + operator + " 4'sh8) / 1'b1; endmodule")
            comparison = comparisons(design)[0]
            self.assertEqual(comparison["width"], 1)
            self.assertEqual([comparison[s]["kind"] for s in ("left", "right")],
                             ["SignedResize", "SignedResize"])
            self.assertEqual([comparison[s]["width"] for s in ("left", "right")], [4, 4])

    def test_source_fixtures_are_admitted(self):
        directory = Path(__file__).resolve().parents[2] / "Examples/system-verilog/wildcard_equality"
        design = lower((directory / "values.sv").read_text())
        self.assertGreater(len(comparisons(design)), 40)
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_nonintegral_operand_stays_loud(self):
        design = lower("module top; real a, b; logic result; initial result = a ==? b; endmodule",
                       require_valid=False)
        self.assertTrue(any(node.get("kind") == "Unsupported" for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
