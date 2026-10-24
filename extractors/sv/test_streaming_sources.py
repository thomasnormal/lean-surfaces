"""Packed streaming sources reorder whole chunks and pad on the right."""
import unittest

from test_packed_assignment_targets import extract_source, nodes
import test_symbolic_continuous_selects as symbolic


class StreamingSources(unittest.TestCase):
    def assignment(self, expression, target="logic [11:0] result;"):
        design = extract_source(
            "module top; logic signed [3:0] hi; logic [3:0] lo; " + target +
            " initial result = " + expression + "; endmodule")
        statement, = [n for n in nodes(design) if n.get("kind") == "BlockingAssign"]
        return statement["value"]

    def test_source_order_and_right_padding(self):
        for size in ("", "3", "16"):
            with self.subTest(size=size):
                value = self.assignment("{>>" + size + "{hi, lo}}")
                self.assertEqual(value["kind"], "Concat")
                self.assertEqual([p.get("name", p.get("bits"))
                                  for p in value["parts"]], ["hi", "lo", "0000"])
                self.assertEqual(value["width"], 12)

    def test_two_state_destination_converts_after_packing(self):
        value = self.assignment("{>>{hi, lo}}", "bit [11:0] result;")
        self.assertEqual(value["kind"], "Squash2")
        self.assertEqual(value["operand"]["parts"][-1]["bits"], "0000")

    def test_whole_packed_struct_source_is_one_vector(self):
        design = extract_source(
            "module top; struct packed { logic [3:0] hi, lo; } packet; "
            "logic [7:0] result; initial result = {>>{packet}}; endmodule")
        self.assertFalse(any(n.get("kind") == "Unsupported" for n in nodes(design)))

    def test_unadmitted_stream_forms_stay_loud(self):
        for expression in ("{>>{{>>{hi}}, lo}}", "{>>{hi++}}", "{<<3{hi++}}"):
            with self.subTest(expression=expression):
                self.assertEqual(self.assignment(expression)["kind"], "Unsupported")
        narrow = extract_source(
            "module top; logic [7:0] source; logic [3:0] result; "
            "initial result = {>>{source}}; endmodule")
        self.assertTrue(any(n.get("kind") == "Unsupported" for n in nodes(narrow)))
        design = extract_source(
            "module top; logic [3:0] data[2]; logic [7:0] result; "
            "initial result = {>>{data with [0:1]}}; endmodule")
        self.assertTrue(any(n.get("sv_kind") == "ConversionExpression:StreamingConcat"
                            for n in nodes(design)))

    def test_symbolic_procedural_and_continuous_sources(self):
        for assignment in ("assign", "always_comb"):
            with self.subTest(assignment=assignment):
                envelope = symbolic.SymbolicContinuousSelects().extract(
                    "module top(input logic [3:0] hi, lo, "
                    "output logic [11:0] result); " + assignment +
                    " result = {>>3{hi, lo}}; endmodule")
                process, = envelope["design"]["modules"][0]["processes"]
                statement = process if assignment == "assign" else process["body"]
                self.assertEqual(statement["value"]["kind"], "Concat")
                self.assertEqual(statement["value"]["parts"][-1]["bits"], "0000")

    def test_symbolic_explicit_right_slice_target_keeps_equal_windows(self):
        envelope = symbolic.SymbolicContinuousSelects().extract(
            "module top(input logic [31:0] source, "
            "output logic [7:0] a, b, c, d); "
            "assign {>>byte {a, b, c, d}} = source; endmodule")
        process, = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(process["target"]["kind"], "ConcatTarget")
        self.assertEqual(process["target"]["width"], 32)
        self.assertEqual([part["name"] for part in process["target"]["parts"]],
                         ["a", "b", "c", "d"])

    def test_symbolic_parameter_widths_stay_loud(self):
        envelope = symbolic.SymbolicContinuousSelects().extract(
            "module top #(parameter W=4) (input logic [W-1:0] source, "
            "output logic [2*W-1:0] result); "
            "assign result = {>>{source}}; endmodule")
        self.assertTrue(any(n.get("sv_kind") == "ConversionExpression:StreamingConcat"
                            for n in nodes(envelope)))

    def test_left_stream_final_short_chunk_precedes_destination_padding(self):
        value = self.assignment("{<<3{hi, lo}}")
        self.assertEqual([p["width"] for p in value["parts"]], [3, 3, 2, 4])
        self.assertEqual([int(p["index"]["bits"], 2) for p in value["parts"][:-1]],
                         [0, 3, 6])
        self.assertEqual(value["parts"][-1]["bits"], "0000")

    def test_left_stream_wide_slice_preserves_the_whole_source(self):
        value = self.assignment("{<<16{hi, lo}}")
        self.assertEqual([p.get("name", p.get("bits")) for p in value["parts"]],
                         ["hi", "lo", "0000"])

    def test_symbolic_left_stream_default_bit_order(self):
        envelope = symbolic.SymbolicContinuousSelects().extract(
            "module top(input logic [3:0] source, output logic [3:0] result); "
            "assign result = {<<{source}}; endmodule")
        process, = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([(p["msb"]["value"], p["lsb"]["value"])
                          for p in process["value"]["parts"]],
                         [(0, 0), (1, 1), (2, 2), (3, 3)])


if __name__ == "__main__":
    unittest.main()
