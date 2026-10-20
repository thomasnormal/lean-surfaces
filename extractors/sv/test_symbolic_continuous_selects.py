"""Constant selected continuous drivers stay in the existing sv-0.2 window tier."""
import json
import tempfile
import unittest
from pathlib import Path

import extract


class SymbolicContinuousSelects(unittest.TestCase):
    def extract(self, source):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            return json.loads(out.read_text())

    def test_disjoint_constant_parts_keep_windows(self):
        envelope = self.extract(
            "module top(input logic [3:0] nibble, output logic [7:0] value); "
            "assign value[3:0] = nibble; assign value[7:4] = 4'ha; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([p["target"]["kind"] for p in processes],
                         ["PartSel", "PartSel"])
        self.assertEqual([(p["target"]["msb"]["value"],
                           p["target"]["lsb"]["value"]) for p in processes],
                         [(3, 0), (7, 4)])

    def test_disjoint_constant_bits_keep_windows(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, input logic flag, "
            "output logic [7:0] value); "
            "assign value[1] = source[0]; assign value[6] = flag; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([p["target"]["kind"] for p in processes],
                         ["BitSel", "BitSel"])
        self.assertEqual([p["target"]["index"]["value"] for p in processes],
                         [1, 6])

    def test_untagged_packed_member_is_a_fixed_window(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output logic [7:0] out, "
            "output logic [3:0] low); "
            "struct packed { logic [3:0] hi; logic [3:0] lo; } value; "
            "assign value.lo = source; assign value.hi = 4'ha; "
            "assign out = value; assign low = value.lo; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([p["target"]["kind"] for p in processes[:2]],
                         ["PartSel", "PartSel"])
        self.assertEqual([(p["target"]["msb"]["value"],
                           p["target"]["lsb"]["value"]) for p in processes[:2]],
                         [(3, 0), (7, 4)])
        self.assertEqual(processes[3]["value"]["kind"], "PartSel")

    def test_packed_struct_typedef_is_compile_time_metadata(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output logic [7:0] out); "
            "typedef struct packed { logic [3:0] hi; logic [3:0] lo; } T; "
            "T value; assign value.lo = source; assign value.hi = 4'ha; "
            "assign out = value; endmodule")
        module = envelope["design"]["modules"][0]
        self.assertEqual([decl["kind"] for decl in module["decls"]], ["Var"])
        self.assertEqual([proc["kind"] for proc in module["processes"]],
                         ["Assign", "Assign", "Assign"])

    def test_nested_packed_member_flattens_to_outer_window(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output logic [7:0] out); "
            "struct packed { struct packed { logic [3:0] hi; "
            "logic [3:0] lo; } inner; } value; "
            "assign value.inner.lo = source; assign value.inner.hi = 4'ha; "
            "assign out = value; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([(p["target"]["msb"]["value"],
                           p["target"]["lsb"]["value"]) for p in processes[:2]],
                         [(3, 0), (7, 4)])

    def test_literal_indexed_parts_normalize_to_windows(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output logic [7:0] value); "
            "assign value[0 +: 4] = source; assign value[7 -: 4] = 4'ha; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([(p["target"]["msb"]["value"],
                           p["target"]["lsb"]["value"]) for p in processes],
                         [(3, 0), (7, 4)])

    def test_dynamic_indexed_parts_stay_loud(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, input logic [2:0] base, "
            "output logic [7:0] value); "
            "assign value[base +: 4] = source; endmodule")
        process, = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(process["kind"], "Unsupported")

    def test_untagged_packed_union_aliases_one_vector(self):
        envelope = self.extract(
            "module top(input logic [7:0] source, output logic [7:0] out, "
            "output logic [7:0] alt); "
            "union packed { logic [7:0] bytes; logic [7:0] alt; } value; "
            "assign value.bytes = source; assign out = value; "
            "assign alt = value.alt; endmodule")
        module = envelope["design"]["modules"][0]
        self.assertEqual(module["decls"][0]["width"]["resolved"], 8)
        self.assertEqual([proc["kind"] for proc in module["processes"]],
                         ["Assign", "Assign", "Assign"])

    def test_packed_union_typedef_is_compile_time_metadata(self):
        envelope = self.extract(
            "module top(input logic [7:0] source, output logic [7:0] out); "
            "typedef union packed { logic [7:0] bytes; logic [7:0] alt; } U; "
            "U value; assign value.bytes = source; assign out = value; endmodule")
        module = envelope["design"]["modules"][0]
        self.assertEqual([decl["kind"] for decl in module["decls"]], ["Var"])
        self.assertEqual([proc["kind"] for proc in module["processes"]],
                         ["Assign", "Assign"])

    def test_noncanonical_constant_parts_normalize_offsets(self):
        envelope = self.extract(
            "module top(input logic [10:3] source, output logic [10:3] value); "
            "assign value[6:3] = source[10:7]; "
            "assign value[10:7] = source[6:3]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([(p["target"]["msb"]["value"],
                           p["target"]["lsb"]["value"],
                           p["value"]["msb"]["value"],
                           p["value"]["lsb"]["value"]) for p in processes],
                         [(3, 0, 7, 4), (7, 4, 3, 0)])

    def test_noncanonical_constant_bits_normalize_offsets(self):
        envelope = self.extract(
            "module top(input logic [10:3] source, output logic [10:3] value); "
            "assign value[3] = source[10]; assign value[10] = source[3]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([p["target"]["index"]["value"] for p in processes],
                         [0, 7])
        self.assertEqual([p["value"]["index"]["value"] for p in processes],
                         [7, 0])

    def test_noncanonical_dynamic_bits_stay_loud(self):
        envelope = self.extract(
            "module top(input logic [10:3] source, input logic [2:0] index, "
            "output logic [10:3] value); assign value[index] = source[3]; endmodule")
        process, = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(process["kind"], "Unsupported")


if __name__ == "__main__":
    unittest.main()
