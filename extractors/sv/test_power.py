"""Integral power keeps the exponent self-determined and independently typed."""
from pathlib import Path
import unittest

from test_bit_queries import lower, nodes
from test_division import symbolic


def powers(design):
    return [node for node in nodes(design) if node.get("kind") == "Binary"
            and "**" in node.get("op", "")]


class Power(unittest.TestCase):
    def test_fixtures_are_admitted(self):
        sources = sorted((Path(__file__).resolve().parents[2] /
                          "harness/sv/power").glob("*.sv"))
        self.assertEqual(len(sources), 3)
        for source in sources:
            with self.subTest(source=source.name):
                self.assertFalse(any(node.get("kind") == "Unsupported"
                                     for node in nodes(lower(source.read_text()))))

    def test_operand_signedness_is_independent(self):
        for signed_base in (False, True):
            for signed_exponent in (False, True):
                design = lower("module top; logic " +
                               ("signed " if signed_base else "") + "[7:0] base; logic " +
                               ("signed " if signed_exponent else "") + "[3:0] exponent; "
                               "logic [15:0] result; initial result = base ** exponent; endmodule")
                power = powers(design)[0]
                self.assertEqual(power["op"], ("s" if signed_base else "u") + "**" +
                                 ("s" if signed_exponent else "u"))
                self.assertEqual(power["width"], 16)
                self.assertEqual(power["left"]["width"], 16)
                self.assertEqual(power["right"]["width"], 4)

    def test_narrowing_follows_power(self):
        design = lower("module top; logic [7:0] base; logic [15:0] exponent; "
                       "logic [3:0] result; initial result = base ** exponent; endmodule")
        self.assertEqual(powers(design)[0]["width"], 8)
        self.assertEqual(powers(design)[0]["right"]["width"], 16)
        value = design["modules"][0]["processes"][0]["body"]["value"]
        self.assertEqual((value["kind"], value["width"]), ("Resize", 4))

    def test_real_power_stays_loud(self):
        design = lower("module top; real base, exponent, result; "
                       "initial result = base ** exponent; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_symbolic_runtime_power_is_typed(self):
        design = symbolic("module divider #(parameter W = 8) "
                          "(input logic [W-1:0] base, output logic [W-1:0] result); "
                          "assign result = base ** 2; endmodule")
        self.assertEqual([node["op"] for node in powers(design)], ["u**s"])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_symbolic_constant_power_keeps_integer_operator(self):
        design = symbolic("module divider #(parameter W = 8); "
                          "localparam P = 2 ** W; logic [P-1:0] value; endmodule")
        self.assertEqual([node["op"] for node in powers(design)], ["**"])

    def test_invalid_source_cannot_hide_power(self):
        design = lower("module top; logic [7:0] base, result; "
                       "initial result = base ** 2; initial missing = 1; endmodule",
                       require_valid=False)
        self.assertIn("Power:invalid-compilation", [node.get("sv_kind") for node in nodes(design)])

    def test_invalid_symbolic_source_cannot_hide_power(self):
        design = symbolic("module divider; logic [7:0] base, result; "
                          "assign result = base ** 2; initial missing = 1; endmodule")
        self.assertIn("Power:invalid-compilation", [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
