"""IEEE 1800-2023 §11.4.10 integral shift admission."""

import unittest
from pathlib import Path

from test_bit_queries import lower, nodes
from test_division import symbolic


class Shifts(unittest.TestCase):
    def test_runtime_shift_operators_are_admitted(self):
        design = lower(
            "module top; logic [7:0] a; logic signed [7:0] s; logic [2:0] n; "
            "initial begin a = a << n; a = a >> n; a = a <<< n; "
            "s = s >>> n; end endmodule"
        )
        unsupported = [node.get("sv_kind") for node in nodes(design)
                       if node.get("kind") == "Unsupported"]
        self.assertNotIn("BinaryExpression:shift", unsupported)
        binaries = [node for node in nodes(design) if node.get("kind") == "Binary"]
        self.assertEqual([node["op"] for node in binaries], ["u<<", "u>>", "u<<<", "s>>>"])

    def test_shift_result_keeps_left_width(self):
        design = lower(
            "module top; logic [7:0] a; logic [3:0] n; "
            "initial a = a << n; endmodule"
        )
        binary = next(node for node in nodes(design) if node.get("kind") == "Binary")
        self.assertEqual(binary["width"], 8)

    def test_symbolic_runtime_shift_is_typed(self):
        design = symbolic(
            "module divider #(parameter W = 8) (input logic clk, input logic [W-1:0] a); "
            "logic [W-1:0] y; always_ff @(posedge clk) y <= a << 1; endmodule"
        )
        self.assertIn("u<<", [node.get("op") for node in nodes(design)])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_fixture_is_admitted(self):
        source = Path(__file__).resolve().parents[2] / "harness/sv/shifts/shifts.sv"
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(lower(source.read_text()))))

    def test_amount_signedness_does_not_change_left_signedness(self):
        for operator in ("<<", ">>", "<<<", ">>>"):
            for signed_amount in (False, True):
                design = lower("module top; logic signed [7:0] value, result; logic " +
                               ("signed " if signed_amount else "") + "[3:0] amount; " +
                               "initial result = value " + operator + " amount; endmodule")
                binary = next(node for node in nodes(design) if node.get("kind") == "Binary")
                self.assertEqual(binary["op"], "s" + operator)
                self.assertEqual(binary["right"]["width"], 4)

    def test_unsigned_comparison_context_changes_sign_fill(self):
        design = lower("module top; logic signed [7:0] value; logic [3:0] amount; "
                       "initial if ((value >>> amount) !== 8'b0) $display(\"FAIL\"); endmodule")
        shift = next(node for node in nodes(design) if node.get("op") == "u>>>")
        self.assertEqual(shift["left"]["name"], "value")

    def test_widening_affects_left_but_not_amount(self):
        design = lower("module top; logic [7:0] value; logic [3:0] amount; "
                       "logic [15:0] result; initial result = value << amount; endmodule")
        shift = next(node for node in nodes(design) if node.get("op") == "u<<")
        self.assertEqual((shift["width"], shift["left"]["width"], shift["right"]["width"]),
                         (16, 16, 4))

    def test_narrowing_follows_the_shift(self):
        design = lower("module top; logic [7:0] value; logic [3:0] amount, result; "
                       "initial result = value >> amount; endmodule")
        assignment = design["modules"][0]["processes"][0]["body"]
        self.assertEqual((assignment["value"]["kind"], assignment["value"]["width"]),
                         ("Resize", 4))
        shift = next(node for node in nodes(design) if node.get("op") == "u>>")
        self.assertEqual(shift["width"], 8)

    def test_scalar_compound_shifts_are_typed(self):
        design = lower("module top; logic signed [7:0] value; logic [3:0] amount; "
                       "initial begin value <<= amount; value >>= amount; "
                       "value <<<= amount; value >>>= amount; end endmodule")
        self.assertEqual([node["op"] for node in nodes(design) if node.get("kind") == "Binary"],
                         ["s<<", "s>>", "s<<<", "s>>>"])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_selected_compound_shift_stays_loud(self):
        design = lower("module top; logic [7:0] value; initial value[3:0] <<= 1; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_symbolic_constant_shift_keeps_integer_operator(self):
        design = symbolic("module divider #(parameter W = 8); localparam P = W << 1; "
                          "logic [P-1:0] value; endmodule")
        self.assertIn("<<", [node.get("op") for node in nodes(design)])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_symbolic_signed_cast_retains_runtime_operator(self):
        design = symbolic("module divider #(parameter W = 8) "
                          "(input logic [7:0] value, input logic [3:0] amount, "
                          "output logic [W-1:0] result); "
                          "assign result = $signed(value) >>> amount; endmodule")
        self.assertIn("s>>>", [node.get("op") for node in nodes(design)])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_invalid_source_cannot_hide_a_shift(self):
        design = lower("module top; logic [7:0] value; initial value = value << 1; "
                       "initial missing = 1; endmodule", require_valid=False)
        self.assertIn("Shift:invalid-compilation", [node.get("sv_kind") for node in nodes(design)])

    def test_invalid_symbolic_source_cannot_hide_a_shift(self):
        design = symbolic("module divider; logic [7:0] value; assign value = value >> 1; "
                          "initial missing = 1; endmodule")
        self.assertIn("Shift:invalid-compilation", [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
