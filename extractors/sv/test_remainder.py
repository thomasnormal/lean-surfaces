"""Typed vector remainder, distinct from constant integer elaboration."""
import json
from pathlib import Path
import tempfile
import unittest

import extract
from test_bit_queries import lower, nodes


def remainders(design):
    return [node for node in nodes(design) if node.get("kind") == "Binary"
            and node.get("op") in ("%", "u%", "s%")]


def symbolic(source):
    with tempfile.TemporaryDirectory() as directory:
        source_path = Path(directory) / "remainder.sv"
        output_path = Path(directory) / "remainder.sv.json"
        source_path.write_text(source)
        extract.process_symbolic("remainder", [str(source_path)], [], str(output_path))
        return json.loads(output_path.read_text())["design"]


class Remainder(unittest.TestCase):
    def test_signed_and_mixed_operands_choose_distinct_value_operators(self):
        design = lower("module top; logic signed [7:0] left, right; "
                       "logic [7:0] unsigned_value, result; initial begin "
                       "result = left % right; result = left % unsigned_value; end endmodule")
        self.assertEqual([node["op"] for node in remainders(design)], ["s%", "u%"])

    def test_widening_happens_before_signed_remainder(self):
        design = lower("module top; logic signed [3:0] left, right; "
                       "logic [7:0] result; initial result = left % right; endmodule")
        remainder = remainders(design)[0]
        self.assertEqual(remainder["width"], 8)
        self.assertEqual([remainder[side]["kind"] for side in ("left", "right")],
                         ["SignedResize", "SignedResize"])

    def test_compound_remainder_reads_original_target(self):
        design = lower("module top; logic [7:0] value, factor; "
                       "initial value %= factor; endmodule")
        remainder = remainders(design)[0]
        self.assertEqual(remainder["op"], "u%")
        self.assertEqual(remainder["left"]["name"], "value")
        self.assertEqual(remainder["right"]["name"], "factor")

    def test_real_remainder_stays_loud(self):
        design = lower("module top; real left, right, result; "
                       "initial result = left % right; endmodule", require_valid=False)
        self.assertTrue(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_invalid_compilation_cannot_hide_remainder(self):
        design = lower("module top; logic [7:0] left, right, result; "
                       "initial result = left % right; initial missing = 1; endmodule",
                       require_valid=False)
        self.assertIn("Remainder:invalid-compilation",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_symbolic_runtime_uses_typed_operator(self):
        design = symbolic("module remainder #(parameter W = 8) "
                          "(input logic [W-1:0] left, right, "
                          "output logic [W-1:0] result); "
                          "assign result = left % right; endmodule")
        self.assertEqual([node["op"] for node in remainders(design)], ["u%"])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_symbolic_signed_runtime_keeps_signed_operands(self):
        design = symbolic("module remainder #(parameter W = 8) "
                          "(input logic signed [W-1:0] left, right, "
                          "output logic signed [W-1:0] result); "
                          "assign result = left % right; endmodule")
        remainder = remainders(design)[0]
        self.assertEqual(remainder["op"], "s%")
        self.assertEqual([remainder[side]["kind"] for side in ("left", "right")],
                         ["Ident", "Ident"])

    def test_symbolic_constant_position_keeps_integer_operator(self):
        design = symbolic("module remainder #(parameter W = 8); "
                          "localparam P = W % 3; logic [P-1:0] value; endmodule")
        self.assertEqual([node["op"] for node in remainders(design)], ["%"])


if __name__ == "__main__":
    unittest.main()
