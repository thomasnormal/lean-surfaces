"""Legacy continuous assignments use fixed vector windows only."""
import json
import tempfile
import unittest
from pathlib import Path

import extract


class LegacyContinuousWindows(unittest.TestCase):
    def extract(self, source):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_file(str(src))
            return json.loads(out.read_text())

    def test_constant_packed_part_is_a_continuous_window(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output logic [7:0] out); "
            "logic [7:0] value; assign value[3:0] = source; assign out = value; "
            "endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual(processes[0]["target"]["kind"], "SelectTarget")
        self.assertEqual(processes[0]["target"]["index"]["bits"],
                         "00000000000000000000000000000000")

    def test_constant_packed_member_is_a_continuous_window(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [1:0] out); "
            "struct packed { logic [1:0] hi; logic [1:0] lo; } value; "
            "assign value.lo = source; assign out = value.lo; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([p["target"]["kind"] for p in processes],
                         ["SelectTarget", "Ident"])
        self.assertEqual(processes[0]["target"]["width"], 2)

    def test_constant_concatenation_is_a_continuous_window_group(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output logic [3:0] out); "
            "logic [1:0] hi, lo; assign {hi, lo} = source; "
            "assign out = {hi, lo}; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual(processes[0]["target"]["kind"], "ConcatTarget")

    def test_constant_fixed_array_cell_is_a_continuous_identifier(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output logic [3:0] out); "
            "logic [3:0] value [0:0]; assign value[0] = source; "
            "assign out = value[0]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual(processes[0]["target"], {
            "kind": "Ident",
            "span": processes[0]["target"]["span"],
            "width": 4,
            "name": "value[0]",
        })

    def test_overlapping_continuous_windows_are_loud(self):
        envelope = self.extract(
            "module top(input logic [7:0] source, output logic [7:0] out); "
            "logic [7:0] value; assign value[7:4] = source[7:4]; "
            "assign value[5:0] = source[5:0]; assign out = value; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual(processes[1]["kind"], "Unsupported")
        self.assertEqual(processes[1]["sv_kind"], "AssignmentExpression:target")

    def test_dynamic_continuous_window_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [1:0] index, input logic source, "
            "output logic out); logic [3:0] value; "
            "assign value[index] = source; assign out = value[0]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Unsupported")

    def test_dynamic_continuous_array_cell_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [1:0] index, input logic source, "
            "output logic out); logic [3:0] value [0:1]; "
            "assign value[index] = {3'b000, source}; "
            "assign out = value[0][0]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Unsupported")

    def test_dynamic_continuous_concatenation_leaf_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [1:0] index, input logic source, "
            "output logic [3:0] out); logic [3:0] value; logic bit0; "
            "assign {value[index], bit0} = {source, source}; "
            "assign out = value; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Unsupported")


if __name__ == "__main__":
    unittest.main()
