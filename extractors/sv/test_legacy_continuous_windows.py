"""Legacy continuous assignments use fixed vector and cell windows."""
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

    def test_constant_fixed_array_cell_select_is_a_continuous_window(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [1:0] out); "
            "logic [3:0] value [0:0]; "
            "assign value[0][1 +: 2] = source; "
            "assign out = value[0][3:2]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        target, readback = processes
        self.assertEqual(target["kind"], "Assign")
        self.assertEqual(target["target"]["kind"], "SelectTarget")
        self.assertEqual(target["target"]["value"]["name"], "value[0]")
        self.assertEqual(target["target"]["index"]["bits"],
                         "0" * 31 + "1")
        self.assertFalse(target["target"]["descending"])
        self.assertEqual(readback["value"]["kind"], "SelectRead")
        self.assertEqual(readback["value"]["value"]["name"], "value[0]")

    def test_noncanonical_fixed_array_cell_window_normalizes(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic out); "
            "logic [10:7] value [0:0]; "
            "assign value[0][10:9] = source; "
            "assign out = value[0][10]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        target, readback = processes
        self.assertEqual(target["target"]["kind"], "SelectTarget")
        self.assertEqual(target["target"]["value"]["name"], "value[0]")
        self.assertEqual(target["target"]["index"]["bits"],
                         "0" * 30 + "10")
        self.assertEqual(readback["value"]["kind"], "SelectRead")
        self.assertEqual(readback["value"]["index"]["bits"],
                         "0" * 30 + "11")

    def test_nested_packed_struct_member_is_a_continuous_window(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [1:0] out); "
            "struct packed { struct packed { logic [1:0] hi; "
            "logic [1:0] lo; } inner; } value; "
            "assign value.inner.lo = source; "
            "assign out = value.inner.lo; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        target, readback = processes
        self.assertEqual(target["target"]["kind"], "SelectTarget")
        self.assertEqual(target["target"]["value"]["name"], "value")
        self.assertEqual(target["target"]["width"], 2)
        self.assertEqual(readback["value"]["kind"], "SelectRead")
        self.assertEqual(readback["value"]["value"]["name"], "value")

    def test_nested_packed_noncanonical_member_selection_flattens(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic out); "
            "struct packed { struct packed { logic [10:7] hi; "
            "logic [1:0] lo; } inner; } value; "
            "assign value.inner.hi[10:9] = source; "
            "assign out = value.inner.hi[10]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        target, readback = processes
        self.assertEqual(target["target"]["index"]["bits"],
                         "0" * 29 + "100")
        self.assertEqual(readback["value"]["kind"], "SelectRead")
        self.assertEqual(readback["value"]["index"]["bits"],
                         "0" * 29 + "101")

    def test_fixed_array_nested_member_selection_flattens(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [1:0] out); "
            "struct packed { logic [3:0] hi; logic [3:0] lo; } "
            "value [0:0]; assign value[0].lo[3:2] = source; "
            "assign out = value[0].lo[3:2]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        target, readback = processes
        self.assertEqual(target["target"]["value"]["name"], "value[0]")
        self.assertEqual(target["target"]["index"]["bits"],
                         "0" * 30 + "10")
        self.assertEqual(readback["value"]["value"]["name"], "value[0]")

    def test_dynamic_nested_member_selection_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, input logic [2:0] index, "
            "output logic out); struct packed { logic [3:0] hi; "
            "logic [1:0] lo; } value; assign value.hi[index] = source[0]; "
            "assign out = value.hi[0]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Unsupported")

    def test_nested_packed_union_member_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [1:0] out); "
            "struct packed { union packed { logic [3:0] all; "
            "logic [1:0] lo; } inner; } value; "
            "assign value.inner.lo = source; "
            "assign out = value.inner.lo; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertTrue(all(process["kind"] == "Unsupported"
                            for process in processes))

    def test_overlapping_fixed_array_cell_windows_are_loud(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [3:0] out); "
            "logic [3:0] value [0:0]; "
            "assign value[0][3:2] = source; "
            "assign value[0][2:1] = source; "
            "assign out = value[0]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual(processes[1]["kind"], "Unsupported")
        self.assertEqual(processes[1]["sv_kind"],
                         "AssignmentExpression:target")

    def test_dynamic_or_effectful_fixed_array_cell_window_stays_loud(self):
        dynamic = self.extract(
            "module top(input logic [1:0] index, input logic source, "
            "output logic out); logic [3:0] value [0:0]; "
            "assign value[0][index] = source; assign out = value[0][0]; "
            "endmodule")
        effectful = self.extract(
            "module top(input logic [1:0] index, input logic source, "
            "output logic out); logic [3:0] value [0:0]; "
            "assign value[0][index++] = source; assign out = value[0][0]; "
            "endmodule")
        for envelope in (dynamic, effectful):
            process = envelope["design"]["modules"][0]["processes"][0]
            self.assertEqual(process["kind"], "Unsupported")

    def test_right_streaming_fixed_array_cell_is_a_continuous_concat(self):
        envelope = self.extract(
            "module top(input logic [4:0] source, output logic out); "
            "logic [3:0] value [0:1]; "
            "assign {>>{value[0], out}} = source; endmodule")
        process, = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(process["kind"], "Assign")
        self.assertEqual(process["target"]["kind"], "ConcatTarget")
        self.assertEqual([part["name"] for part in process["target"]["parts"]],
                         ["value[0]", "out"])

    def test_right_streaming_cell_window_and_member_are_continuous_leaves(self):
        cell = self.extract(
            "module top(input logic [2:0] source, output logic out); "
            "logic [3:0] value [0:1]; "
            "assign {>>{value[0][3:2], out}} = source; endmodule")
        process, = cell["design"]["modules"][0]["processes"]
        self.assertEqual(process["target"]["kind"], "ConcatTarget")
        self.assertEqual(process["target"]["parts"][0]["kind"],
                         "SelectTarget")
        member = self.extract(
            "module top(input logic [2:0] source, output logic out); "
            "struct packed { logic [1:0] hi; logic [1:0] lo; } "
            "value [0:1]; assign {>>{value[0].lo, out}} = source; endmodule")
        process, = member["design"]["modules"][0]["processes"]
        self.assertEqual(process["target"]["kind"], "ConcatTarget")
        self.assertEqual(process["target"]["parts"][0]["kind"],
                         "SelectTarget")

    def test_nonright_or_dynamic_streaming_cell_stays_loud(self):
        sources = (
            "module top(input logic [4:0] source, output logic out); "
            "logic [3:0] value [0:1]; "
            "assign {<<{value[0], out}} = source; endmodule",
            "module top(input logic [4:0] source, output logic out); "
            "logic [3:0] value [0:1]; "
            "assign {>>2{value[0], out}} = source; endmodule",
            "module top(input logic [1:0] index, input logic [4:0] source, "
            "output logic out); logic [3:0] value [0:1]; "
            "assign {>>{value[index], out}} = source; endmodule",
        )
        for source in sources:
            envelope = self.extract(source)
            process, = envelope["design"]["modules"][0]["processes"]
            self.assertEqual(process["kind"], "Unsupported")

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
