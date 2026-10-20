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

    def test_overlapping_constant_drivers_stay_loud(self):
        envelope = self.extract(
            "module top(input logic [7:0] source, output logic [7:0] value); "
            "assign value[7:4] = source[7:4]; "
            "assign value[5:0] = source[5:0]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual(processes[1]["kind"], "Unsupported")
        self.assertEqual(processes[1]["sv_kind"], "AssignmentExpression:target")

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

    def test_member_subrange_flattens_to_outer_window(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [3:0] out); "
            "struct packed { logic [3:0] hi; logic [3:0] lo; } value; "
            "assign value.hi[1:0] = source; assign out = value.hi; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (5, 4))
        self.assertEqual(processes[1]["value"]["kind"], "PartSel")

    def test_member_bit_flattens_to_outer_window(self):
        envelope = self.extract(
            "module top(input logic source, output logic [3:0] out); "
            "struct packed { logic [3:0] hi; logic [3:0] lo; } value; "
            "assign value.hi[0] = source; assign out = value.hi; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (4, 4))

    def test_union_member_subrange_flattens_to_alias_window(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [3:0] out); "
            "union packed { logic [3:0] bytes; logic [3:0] alt; } value; "
            "assign value.bytes[1:0] = source; assign out = value.alt; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (1, 0))
        self.assertEqual(processes[1]["value"]["kind"], "PartSel")

    def test_union_member_bit_flattens_to_alias_window(self):
        envelope = self.extract(
            "module top(input logic source, output logic [3:0] out); "
            "union packed { logic [3:0] bytes; logic [3:0] alt; } value; "
            "assign value.bytes[0] = source; assign out = value.alt; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (0, 0))
        self.assertEqual(processes[1]["value"]["kind"], "PartSel")

    def test_member_indexed_parts_flatten_to_outer_windows(self):
        envelope = self.extract(
            "module top(input logic [1:0] low, input logic [1:0] high, "
            "output logic [3:0] out); "
            "struct packed { logic [3:0] hi; logic [3:0] lo; } value; "
            "assign value.hi[0 +: 2] = low; "
            "assign value.hi[3 -: 2] = high; assign out = value.hi; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([(p["target"]["msb"]["value"],
                           p["target"]["lsb"]["value"]) for p in processes[:2]],
                         [(5, 4), (7, 6)])

    def test_member_indexed_parts_noncanonical_stay_loud(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [3:0] out); "
            "struct packed { logic [0:3] hi; logic [3:0] lo; } value; "
            "assign value.hi[0 +: 2] = source; assign out = value.lo; endmodule")
        process, = envelope["design"]["modules"][0]["processes"][:1]
        self.assertEqual(process["kind"], "Unsupported")

    def test_union_member_indexed_parts_flatten_to_alias_windows(self):
        envelope = self.extract(
            "module top(input logic [1:0] low, input logic [1:0] high, "
            "output logic [3:0] out); "
            "union packed { logic [3:0] bytes; logic [3:0] alt; } value; "
            "assign value.bytes[0 +: 2] = low; "
            "assign value.bytes[3 -: 2] = high; assign out = value.alt; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([(p["target"]["msb"]["value"],
                           p["target"]["lsb"]["value"]) for p in processes[:2]],
                         [(1, 0), (3, 2)])

    def test_noncanonical_member_subrange_flattens_offsets(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [3:0] out); "
            "struct packed { logic [10:7] hi; logic [3:0] lo; } value; "
            "assign value.hi[10:9] = source; assign out = value.hi; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (7, 6))

    def test_noncanonical_union_subrange_flattens_alias_offsets(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [3:0] out); "
            "union packed { logic [10:7] bytes; logic [3:0] alt; } value; "
            "assign value.bytes[10:9] = source; assign out = value.alt; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (3, 2))

    def test_noncanonical_member_bit_flattens_offset(self):
        envelope = self.extract(
            "module top(input logic source, output logic [3:0] out); "
            "struct packed { logic [10:7] hi; logic [3:0] lo; } value; "
            "assign value.hi[10] = source; assign out = value.hi; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (7, 7))

    def test_noncanonical_union_bit_flattens_alias_offset(self):
        envelope = self.extract(
            "module top(input logic source, output logic [3:0] out); "
            "union packed { logic [10:7] bytes; logic [3:0] alt; } value; "
            "assign value.bytes[10] = source; assign out = value.alt; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (3, 3))

    def test_typedef_member_indexed_parts_flatten_to_windows(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [3:0] out); "
            "typedef struct packed { logic [3:0] hi; logic [3:0] lo; } T; "
            "T value; assign value.hi[0 +: 2] = source; "
            "assign out = value.hi; endmodule")
        module = envelope["design"]["modules"][0]
        processes = module["processes"]
        self.assertEqual([decl["kind"] for decl in module["decls"]], ["Var"])
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (5, 4))

    def test_union_typedef_member_indexed_parts_flatten_to_alias_windows(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [3:0] out); "
            "typedef union packed { logic [3:0] bytes; logic [3:0] alt; } U; "
            "U value; assign value.bytes[0 +: 2] = source; "
            "assign out = value.alt; endmodule")
        module = envelope["design"]["modules"][0]
        processes = module["processes"]
        self.assertEqual([decl["kind"] for decl in module["decls"]], ["Var"])
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (1, 0))

    def test_noncanonical_typedef_member_subrange_flattens(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [3:0] out); "
            "typedef struct packed { logic [10:7] hi; logic [3:0] lo; } T; "
            "T value; assign value.hi[10:9] = source; "
            "assign out = value.hi; endmodule")
        module = envelope["design"]["modules"][0]
        processes = module["processes"]
        self.assertEqual([decl["kind"] for decl in module["decls"]], ["Var"])
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (7, 6))

    def test_noncanonical_union_typedef_subrange_flattens_alias(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [3:0] out); "
            "typedef union packed { logic [10:7] bytes; logic [3:0] alt; } U; "
            "U value; assign value.bytes[10:9] = source; "
            "assign out = value.alt; endmodule")
        module = envelope["design"]["modules"][0]
        processes = module["processes"]
        self.assertEqual([decl["kind"] for decl in module["decls"]], ["Var"])
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (3, 2))

    def test_noncanonical_typedef_member_bit_flattens(self):
        envelope = self.extract(
            "module top(input logic source, output logic [3:0] out); "
            "typedef struct packed { logic [10:7] hi; logic [3:0] lo; } T; "
            "T value; assign value.hi[10] = source; "
            "assign out = value.hi; endmodule")
        module = envelope["design"]["modules"][0]
        processes = module["processes"]
        self.assertEqual([decl["kind"] for decl in module["decls"]], ["Var"])
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (7, 7))

    def test_noncanonical_typedef_union_bit_flattens_alias(self):
        envelope = self.extract(
            "module top(input logic source, output logic [3:0] out); "
            "typedef union packed { logic [10:7] bytes; logic [3:0] alt; } U; "
            "U value; assign value.bytes[10] = source; "
            "assign out = value.alt; endmodule")
        module = envelope["design"]["modules"][0]
        processes = module["processes"]
        self.assertEqual([decl["kind"] for decl in module["decls"]], ["Var"])
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (3, 3))

    def test_nested_member_indexed_slice_flattens_offsets(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [3:0] out); "
            "struct packed { struct packed { logic [3:0] hi; "
            "logic [3:0] lo; } inner; } value; "
            "assign value.inner.hi[0 +: 2] = source; "
            "assign out = value.inner.hi; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (5, 4))

    def test_nested_member_bit_flattens_offsets(self):
        envelope = self.extract(
            "module top(input logic source, output logic [3:0] out); "
            "struct packed { struct packed { logic [3:0] hi; "
            "logic [3:0] lo; } inner; } value; "
            "assign value.inner.hi[0] = source; "
            "assign out = value.inner.hi; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (4, 4))

    def test_nested_noncanonical_member_subrange_flattens_offsets(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [3:0] out); "
            "struct packed { struct packed { logic [10:7] hi; "
            "logic [3:0] lo; } inner; } value; "
            "assign value.inner.hi[10:9] = source; "
            "assign out = value.inner.hi; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (7, 6))

    def test_nested_noncanonical_member_bit_flattens_offset(self):
        envelope = self.extract(
            "module top(input logic source, output logic [3:0] out); "
            "struct packed { struct packed { logic [10:7] hi; "
            "logic [3:0] lo; } inner; } value; "
            "assign value.inner.hi[10] = source; "
            "assign out = value.inner.hi; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual((processes[0]["target"]["msb"]["value"],
                          processes[0]["target"]["lsb"]["value"]), (7, 7))

    def test_nested_member_concat_flattens_recursive_windows(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output logic [3:0] hi, "
            "output logic [3:0] lo); "
            "struct packed { struct packed { logic [3:0] hi; "
            "logic [3:0] lo; } inner; } value; "
            "assign {value.inner.hi[1:0], value.inner.lo[1:0]} = source; "
            "assign hi = value.inner.hi; assign lo = value.inner.lo; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["target"]["kind"], "ConcatTarget")
        self.assertEqual([(part["msb"]["value"], part["lsb"]["value"])
                          for part in processes[0]["target"]["parts"]],
                         [(5, 4), (1, 0)])

    def test_typedef_nested_member_concat_flattens_windows(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output logic [3:0] hi, "
            "output logic [3:0] lo); "
            "typedef struct packed { struct packed { logic [3:0] hi; "
            "logic [3:0] lo; } inner; } T; T value; "
            "assign {value.inner.hi[1:0], value.inner.lo[1:0]} = source; "
            "assign hi = value.inner.hi; assign lo = value.inner.lo; endmodule")
        module = envelope["design"]["modules"][0]
        processes = module["processes"]
        self.assertEqual([decl["kind"] for decl in module["decls"]], ["Var"])
        self.assertEqual([(part["msb"]["value"], part["lsb"]["value"])
                          for part in processes[0]["target"]["parts"]],
                         [(5, 4), (1, 0)])

    def test_nested_noncanonical_concat_flattens_windows(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output logic [3:0] hi, "
            "output logic [3:0] lo); "
            "struct packed { struct packed { logic [10:7] hi; "
            "logic [10:7] lo; } inner; } value; "
            "assign {value.inner.hi[10:9], value.inner.lo[10:9]} = source; "
            "assign hi = value.inner.hi; assign lo = value.inner.lo; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([(part["msb"]["value"], part["lsb"]["value"])
                          for part in processes[0]["target"]["parts"]],
                         [(7, 6), (3, 2)])

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
