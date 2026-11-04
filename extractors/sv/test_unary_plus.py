"""IEEE 1800-2023 11.4.3: unary plus remains an arithmetic operator."""

import unittest
from pathlib import Path

from test_bit_queries import lower, nodes
from test_division import symbolic

# SYNTHETIC-ORACLE: tests=UnaryPlus | origin=spec | authority=IEEE-1800-2023#11.4.3 | map=nodes:retain-arithmetic-plus-and-elaborated-width


def plus_nodes(design):
    return [node for node in nodes(design)
            if node.get("kind") == "Unary" and node.get("op") == "+"]


class UnaryPlus(unittest.TestCase):
    def test_runtime_plus_is_retained(self):
        design = lower(
            'module e(input logic [3:0] a, output logic [3:0] b); '
            'assign b = +a; endmodule'
        )
        expression = design["modules"][0]["processes"][0]["value"]
        self.assertEqual(expression["kind"], "Unary")
        self.assertEqual(expression["op"], "+")
        self.assertEqual(expression["width"], 4)
        self.assertEqual(expression["operand"]["name"], "a")
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_scalar_signed_and_wide_operands(self):
        for declaration in ("logic", "logic signed [7:0]", "logic [64:0]"):
            with self.subTest(declaration=declaration):
                design = lower("module e; " + declaration + " a, b; initial b = +a; endmodule")
                self.assertEqual(len(plus_nodes(design)), 1)
                self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_symbolic_runtime_plus_is_retained(self):
        design = symbolic("module divider #(parameter W=8) "
                          "(input logic [W-1:0] a, output logic [W-1:0] b); "
                          "assign b = +a; endmodule")
        self.assertEqual(len(plus_nodes(design)), 1)
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_arithmetic_operand_keeps_plus(self):
        design = symbolic("module divider #(parameter W=8) "
                          "(input logic [W-1:0] a, output logic [W-1:0] b); "
                          "assign b = (+a & 8'h80) / 2; endmodule")
        self.assertEqual(len(plus_nodes(design)), 1)
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_reference_fixture_is_admitted(self):
        source = Path(__file__).resolve().parents[2] / "Examples/system-verilog/unary_plus/arithmetic.sv"
        design = lower(source.read_text())
        self.assertGreaterEqual(len(plus_nodes(design)), 10)
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_real_operand_stays_loud(self):
        design = lower("module top; real value, result; initial result = +value; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported" for node in nodes(design)))


if __name__ == "__main__":
    unittest.main()
