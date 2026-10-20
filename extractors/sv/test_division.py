"""Typed vector division, distinct from constant integer elaboration."""
import json
from pathlib import Path
import tempfile
import unittest

import extract
from test_bit_queries import lower, nodes


def divisions(design):
    return [node for node in nodes(design) if node.get("kind") == "Binary"
            and node.get("op") in ("/", "u/", "s/")]


def symbolic(source):
    with tempfile.TemporaryDirectory() as directory:
        source_path = Path(directory) / "divider.sv"
        output_path = Path(directory) / "divider.sv.json"
        source_path.write_text(source)
        extract.process_symbolic("divider", [str(source_path)], [], str(output_path))
        return json.loads(output_path.read_text())["design"]


class Division(unittest.TestCase):
    def test_reference_fixtures_are_admitted(self):
        sources = sorted((Path(__file__).resolve().parents[2] /
                          "harness/sv/division").glob("*.sv"))
        self.assertEqual(len(sources), 4)
        for source in sources:
            with self.subTest(source=source.name):
                design = lower(source.read_text())
                self.assertTrue(divisions(design))
                self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_signed_and_mixed_operands_choose_distinct_value_operators(self):
        design = lower("module top; logic signed [7:0] left, right; "
                       "logic [7:0] unsigned_value, result; initial begin "
                       "result = left / right; result = left / unsigned_value; end endmodule")
        self.assertEqual([node["op"] for node in divisions(design)], ["s/", "u/"])

    def test_widening_happens_before_signed_division(self):
        design = lower("module top; logic signed [3:0] left, right; "
                       "logic [7:0] result; initial result = left / right; endmodule")
        division = divisions(design)[0]
        self.assertEqual(division["width"], 8)
        self.assertEqual([division[side]["kind"] for side in ("left", "right")],
                         ["SignedResize", "SignedResize"])

    def test_narrowing_happens_after_division(self):
        design = lower("module top; logic [7:0] left, right; logic [3:0] result; "
                       "initial result = left / right; endmodule")
        value = design["modules"][0]["processes"][0]["body"]["value"]
        self.assertEqual(value["kind"], "Resize")
        self.assertEqual(value["width"], 4)
        self.assertEqual(divisions(design)[0]["width"], 8)

    def test_compound_signedness_depends_on_both_operands(self):
        design = lower("module top; logic signed [7:0] left, right; "
                       "logic [7:0] unsigned_value; initial begin "
                       "left /= right; left /= unsigned_value; end endmodule")
        self.assertEqual([node["op"] for node in divisions(design)], ["s/", "u/"])

    def test_selected_compound_target_reads_the_selected_value(self):
        design = lower("module top; logic [7:0] value; logic [3:0] factor; "
                       "initial value[3:0] /= factor; endmodule")
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))
        self.assertEqual(divisions(design)[0]['left']['kind'], 'CompoundRead')

    def test_real_division_stays_loud(self):
        design = lower("module top; real left, right, result; "
                       "initial result = left / right; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_invalid_legacy_compilation_cannot_hide_division(self):
        design = lower("module top; logic [7:0] left, right, result; "
                       "initial result = left / right; initial missing = 1; endmodule",
                       require_valid=False)
        self.assertIn("Division:invalid-compilation",
                      [node.get("sv_kind") for node in nodes(design)])

    def test_symbolic_runtime_uses_typed_operator(self):
        design = symbolic("module divider #(parameter W = 8) "
                          "(input logic [W-1:0] left, right, output logic [W-1:0] result); "
                          "assign result = left / right; endmodule")
        self.assertEqual([node["op"] for node in divisions(design)], ["u/"])
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_symbolic_context_preserves_unfolded_signed_constants(self):
        design = symbolic("module divider #(parameter W = 16) "
                          "(input logic [7:0] numerator, output logic [W-1:0] result); "
                          "assign result = (-8'sh80) / 8'sd2; endmodule")
        division = divisions(design)[0]
        self.assertEqual(division["op"], "s/")
        self.assertTrue(any(node.get("kind") == "Unary" for node in nodes(division["left"])))
        self.assertTrue(any(node.get("kind") == "SignedResize" for node in nodes(division)))

    def test_self_determined_signed_comparison_keeps_operand_types(self):
        design = symbolic("module divider #(parameter W = 8) "
                          "(output logic [W-1:0] result); "
                          "assign result = ((-4'sh8) == 4'sh8) / 1'b1; endmodule")
        comparison = next(node for node in nodes(design) if node.get("op") == "==")
        self.assertEqual([comparison[side]["kind"] for side in ("left", "right")],
                         ["SignedResize", "SignedResize"])

    def test_symbolic_constant_position_keeps_integer_operator(self):
        design = symbolic("module divider #(parameter W = 8); "
                          "localparam P = W / 2; logic [P-1:0] value; endmodule")
        self.assertEqual([node["op"] for node in divisions(design)], ["/"])

    def test_symbolic_self_determined_boundaries_retain_runtime_nodes(self):
        design = symbolic("module divider #(parameter W = 8) "
                          "(input logic [W-1:0] value, output logic [31:0] result); "
                          "assign result = {2{(-$signed(value) - 4'sh8)}} / 8'd2; endmodule")
        self.assertEqual([node["op"] for node in divisions(design)], ["u/"])
        self.assertTrue(any(node.get("kind") == "Repl" for node in nodes(design)))
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_selected_constant_positions_do_not_acquire_runtime_markers(self):
        design = symbolic("module divider #(parameter W = 8) "
                          "(input logic [W-1:0] value, output logic [31:0] result); "
                          "assign result = value[(W < 16 ? 3 : 7):0] / 8'd2; endmodule")
        selection = next(node for node in nodes(design) if node.get("kind") == "PartSel")
        self.assertFalse(any(node.get("kind") == "SignedResize" for node in nodes(selection["msb"])))
        self.assertFalse(any(node.get("kind") == "Unsupported" for node in nodes(design)))

    def test_symbolic_invalid_compilation_cannot_hide_division(self):
        design = symbolic("module divider; logic [7:0] left, right, result; "
                          "assign result = left / right; initial missing = 1; endmodule")
        self.assertIn("Division:invalid-compilation",
                      [node.get("sv_kind") for node in nodes(design)])


if __name__ == "__main__":
    unittest.main()
