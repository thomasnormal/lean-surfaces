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

    def test_generated_multidimensional_elements_keep_symbolic_indices(self):
        envelope = self.extract(
            "module top #(parameter N = 4, W = 3) "
            "(output logic [N-1:0][W-1:0] value); "
            "for (genvar j = 0; j < N; j++) begin : cells "
            "assign value[j] = $unsigned(j); end endmodule")
        module = envelope["design"]["modules"][0]
        loop, = module["generates"]
        assignment, = loop["body"]
        self.assertEqual(assignment["kind"], "Assign")
        self.assertEqual(assignment["target"]["kind"], "BitSel")
        self.assertEqual(assignment["target"]["width"], 3)
        self.assertEqual(assignment["target"]["index"]["kind"], "GenvarRef")
        self.assertEqual(assignment["target"]["index"]["name"], "j")

    def test_multidimensional_literal_select_retains_element_index(self):
        envelope = self.extract(
            "module top(input logic [3:0][2:0] source, "
            "output logic [2:0] out); assign out = source[2]; endmodule")
        assignment, = envelope["design"]["modules"][0]["processes"]
        selection = assignment["value"]
        self.assertEqual(selection["kind"], "BitSel")
        self.assertEqual(selection["width"], 3)
        self.assertEqual(selection["index"]["value"], 2)
        self.assertEqual(selection["index"].get("resolved_width"), 32)
        self.assertNotEqual(selection["index"]["span"], selection["span"])

    def test_parameterized_bit_select_is_not_rejected_at_default_width(self):
        envelope = self.extract(
            "module top #(parameter W = 5) (input logic [W-1:0] source, "
            "output logic out); assign out = source[5]; endmodule")
        assignment, = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(assignment["value"]["kind"], "BitSel")
        self.assertEqual(assignment["value"]["index"]["value"], 5)

    def test_parameterized_part_select_is_not_rejected_at_default_width(self):
        envelope = self.extract(
            "module top #(parameter W = 5) (input logic [W-1:0] source, "
            "output logic [1:0] out); assign out = source[6:5]; endmodule")
        assignment, = envelope["design"]["modules"][0]["processes"]
        selection = assignment["value"]
        self.assertEqual(selection["kind"], "PartSel")
        self.assertEqual((selection["msb"]["value"], selection["lsb"]["value"]),
                         (6, 5))

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

    def test_nested_packed_union_member_flattens_to_outer_window(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [1:0] out); "
            "struct packed { union packed { logic [3:0] all; "
            "logic [3:0] alt; } inner; } value; "
            "assign value.inner.alt[1 +: 2] = source; "
            "assign out = value.inner.all[1 +: 2]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([process["kind"] for process in processes],
                         ["Assign", "Assign"])
        self.assertEqual(processes[0]["target"]["kind"], "PartSel")
        self.assertEqual(processes[1]["value"]["kind"], "PartSel")
        self.assertEqual(processes[0]["target"]["msb"]["value"],
                         processes[1]["value"]["msb"]["value"])

    def test_nested_packed_union_overlapping_windows_stay_loud(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [1:0] out); "
            "struct packed { union packed { logic [3:0] all; "
            "logic [3:0] alt; } inner; } value; "
            "assign value.inner.all[1:0] = source; "
            "assign value.inner.alt[1:0] = source; "
            "assign out = value.inner.all[1:0]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual(processes[1]["kind"], "Unsupported")
        self.assertEqual(processes[1]["sv_kind"],
                         "AssignmentExpression:target")

    def test_dynamic_nested_packed_union_selection_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, input logic [2:0] index, "
            "output logic [1:0] out); "
            "struct packed { union packed { logic [3:0] all; "
            "logic [3:0] alt; } inner; } value; "
            "assign value.inner.alt[index +: 2] = source; "
            "assign out = value.inner.all[1:0]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Unsupported")

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

    def test_constant_fixed_array_cell_is_a_symbolic_vector(self):
        envelope = self.extract(
            "module top(input logic source, output logic out); "
            "logic [3:0] arr [0:1]; "
            "assign arr[0] = {3'b000, source}; assign out = arr[0][0]; "
            "endmodule")
        module = envelope["design"]["modules"][0]
        self.assertEqual([decl["name"] for decl in module["decls"]],
                         ["arr[0]", "arr[1]"])
        processes = module["processes"]
        self.assertEqual(processes[0]["target"], {
            "kind": "Ident",
            "span": processes[0]["target"]["span"],
            "width": 4,
            "name": "arr[0]",
        })
        self.assertEqual(processes[1]["value"]["kind"], "BitSel")
        self.assertEqual(processes[1]["value"]["value"]["kind"], "Ident")
        self.assertEqual(processes[1]["value"]["value"]["name"], "arr[0]")

    def test_dynamic_fixed_array_cell_stays_loud(self):
        envelope = self.extract(
            "module top(input logic source, input logic index, "
            "output logic out); logic [3:0] arr [0:1]; "
            "assign arr[index] = {3'b000, source}; assign out = arr[0][0]; "
            "endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Unsupported")

    def test_packed_typedef_fixed_array_cell_is_symbolic_vector(self):
        envelope = self.extract(
            "module top(input logic source, output logic out); "
            "typedef logic [3:0] T; T arr [0:1]; "
            "assign arr[0] = {3'b000, source}; assign out = arr[0][0]; "
            "endmodule")
        module = envelope["design"]["modules"][0]
        self.assertEqual([decl["name"] for decl in module["decls"]],
                         ["arr[0]", "arr[1]"])
        self.assertEqual(module["others"], [])
        self.assertEqual(module["decls"][0]["width"]["packed"][0]["msb"]["value"], 3)
        self.assertEqual(module["processes"][1]["value"]["value"]["name"], "arr[0]")

    def test_enum_fixed_array_cell_is_symbolic_vector(self):
        envelope = self.extract(
            "module top(output logic [1:0] out); "
            "typedef enum logic [1:0] {A = 2'b00, B = 2'b01, C = 2'b10} E; "
            "E arr [0:1]; assign arr[0] = B; assign out = arr[0]; "
            "endmodule")
        module = envelope["design"]["modules"][0]
        self.assertEqual([decl["name"] for decl in module["decls"]],
                         ["arr[0]", "arr[1]"])
        self.assertEqual(module["processes"][0]["target"]["name"], "arr[0]")
        self.assertEqual(module["processes"][0]["value"]["kind"], "EnumRef")

    def test_packed_aggregate_fixed_array_member_is_a_cell_window(self):
        envelope = self.extract(
            "module top(output logic [1:0] struct_out, "
            "output logic [3:0] union_out); "
            "typedef struct packed { logic [1:0] hi; logic [1:0] lo; } S; "
            "typedef union packed { logic [3:0] a; logic [3:0] b; } U; "
            "S sa [0:1]; U ua [0:1]; "
            "assign sa[0].lo = 2'b01; assign struct_out = sa[0].lo; "
            "assign ua[0].a = 4'b1010; assign union_out = ua[0].b; "
            "endmodule")
        module = envelope["design"]["modules"][0]
        self.assertEqual([decl["name"] for decl in module["decls"]],
                         ["sa[0]", "sa[1]", "ua[0]", "ua[1]"])
        self.assertEqual([proc["kind"] for proc in module["processes"]],
                         ["Assign", "Assign", "Assign", "Assign"])
        self.assertEqual(module["processes"][0]["target"]["kind"], "PartSel")
        self.assertEqual(module["processes"][2]["target"]["kind"], "PartSel")

    def test_packed_aggregate_dynamic_array_member_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [0:0] index, output logic [1:0] out); "
            "typedef struct packed { logic [1:0] hi; logic [1:0] lo; } S; "
            "S arr [0:1]; assign arr[index].lo = 2'b01; "
            "assign out = arr[0].lo; endmodule")
        self.assertEqual(envelope["design"]["modules"][0]["processes"][0]["kind"],
                         "Unsupported")

    def test_fixed_array_pattern_initializer_populates_symbolic_cells(self):
        envelope = self.extract(
            "module top(output logic [3:0] first, output logic [3:0] second); "
            "logic [3:0] arr [0:1] = '{4'h1, 4'hx}; "
            "assign first = arr[0]; assign second = arr[1]; endmodule")
        module = envelope["design"]["modules"][0]
        decls = [decl for decl in module["decls"] if decl["kind"] == "Var"]
        self.assertEqual([decl["name"] for decl in decls], ["arr[0]", "arr[1]"])
        self.assertEqual([decl["init"]["bits"] for decl in decls],
                         ["0001", "xxxx"])
        self.assertEqual([proc["value"]["name"] for proc in module["processes"]],
                         ["arr[0]", "arr[1]"])

    def test_fixed_array_structured_initializer_is_elaborated_per_cell(self):
        envelope = self.extract(
            "module top(output logic [3:0] first, output logic [3:0] second); "
            "logic [3:0] arr [0:1] = '{default:4'h2}; "
            "assign first = arr[0]; assign second = arr[1]; endmodule")
        decls = [decl for decl in envelope["design"]["modules"][0]["decls"]
                 if decl["kind"] == "Var"]
        self.assertEqual([decl["init"]["bits"] for decl in decls],
                         ["0010", "0010"])

    def test_fixed_array_replicated_initializer_populates_each_cell(self):
        envelope = self.extract(
            "module top(output logic [3:0] first, output logic [3:0] second); "
            "logic [3:0] arr [0:1] = '{2{4'h3}}; "
            "assign first = arr[0]; assign second = arr[1]; endmodule")
        decls = [decl for decl in envelope["design"]["modules"][0]["decls"]
                 if decl["kind"] == "Var"]
        self.assertEqual([decl["init"]["bits"] for decl in decls],
                         ["0011", "0011"])

    def test_fixed_array_wrong_length_initializer_stays_loud(self):
        envelope = self.extract(
            "module top(output logic [3:0] out); "
            "logic [3:0] arr [0:1] = '{4'h1}; assign out = arr[0]; "
            "endmodule")
        module = envelope["design"]["modules"][0]
        self.assertTrue(any(decl["kind"] == "Unsupported"
                            for decl in module["decls"]))

    def test_fixed_array_aggregate_initializer_stays_loud(self):
        envelope = self.extract(
            "module top(output logic [3:0] out); "
            "typedef struct packed { logic [1:0] hi; logic [1:0] lo; } S; "
            "S arr [0:1] = '{'{2'b01, 2'b10}, '{2'b11, 2'b00}}; "
            "assign out = arr[0]; endmodule")
        module = envelope["design"]["modules"][0]
        self.assertTrue(any(decl["kind"] == "Unsupported"
                            for decl in module["decls"]))

    def test_fixed_array_cell_can_be_a_concat_target_leaf(self):
        envelope = self.extract(
            "module top(input logic [4:0] source, output logic [3:0] hi, "
            "output logic lo); logic [3:0] arr [0:1]; "
            "assign {arr[0], lo} = source; assign hi = arr[0]; "
            "endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        target = processes[0]["target"]
        self.assertEqual(target["kind"], "ConcatTarget")
        self.assertEqual([part["name"] for part in target["parts"]],
                         ["arr[0]", "lo"])
        self.assertEqual(processes[1]["value"]["name"], "arr[0]")

    def test_fixed_array_cell_preserves_noncanonical_packed_slice(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [3:0] out); "
            "logic [10:7] arr [0:1]; assign arr[0][10:9] = source; "
            "assign out = arr[0]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        target = processes[0]["target"]
        self.assertEqual((target["msb"]["value"], target["lsb"]["value"]),
                         (3, 2))
        self.assertEqual(processes[1]["value"]["name"], "arr[0]")

    def test_fixed_array_cell_dynamic_packed_slice_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, input logic [1:0] base, "
            "output logic [3:0] out); logic [3:0] arr [0:1]; "
            "assign arr[0][base +: 2] = source; assign out = arr[0]; "
            "endmodule")
        self.assertEqual(envelope["design"]["modules"][0]["processes"][0]["kind"],
                         "Unsupported")

    def test_fixed_array_reverse_range_keeps_declared_cell_labels(self):
        envelope = self.extract(
            "module top(input logic source, output logic out); "
            "logic [3:0] arr [1:0]; assign arr[0] = {3'b000, source}; "
            "assign out = arr[0][0]; endmodule")
        module = envelope["design"]["modules"][0]
        self.assertEqual([decl["name"] for decl in module["decls"]],
                         ["arr[1]", "arr[0]"])
        self.assertEqual(module["processes"][0]["target"]["name"], "arr[0]")
        self.assertEqual(module["processes"][1]["value"]["value"]["name"], "arr[0]")

    def test_right_streaming_accepts_constant_array_and_packed_leaves(self):
        envelope = self.extract(
            "module top(input logic [4:0] source, output logic [3:0] hi, "
            "output logic out); logic [3:0] arr [0:1]; "
            "always_comb begin {>>{arr[0], out}} = source; end "
            "assign hi = arr[0]; endmodule")
        module = envelope["design"]["modules"][0]
        statement = module["processes"][0]["body"]["stmts"][0]
        target = statement["target"]
        self.assertEqual(target["kind"], "ConcatTarget")
        self.assertEqual([part["name"] for part in target["parts"]],
                         ["arr[0]", "out"])
        self.assertEqual(target["width"], 5)

    def test_right_streaming_accepts_constant_cell_slice(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output logic [1:0] out); "
            "logic [3:0] arr [0:1]; always_comb begin "
            "{>>{arr[0][3:2], out}} = source; end endmodule")
        statement = envelope["design"]["modules"][0]["processes"][0]["body"]["stmts"][0]
        part = statement["target"]["parts"][0]
        self.assertEqual(part["kind"], "PartSel")
        self.assertEqual((part["msb"]["value"], part["lsb"]["value"]), (3, 2))

    def test_right_streaming_dynamic_array_leaf_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [4:0] source, input logic index, "
            "output logic out); logic [3:0] arr [0:1]; always_comb begin "
            "{>>{arr[index], out}} = source; end endmodule")
        statement = envelope["design"]["modules"][0]["processes"][0]["body"]["stmts"][0]
        self.assertEqual(statement["kind"], "Unsupported")

    def test_right_streaming_explicit_slice_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [4:0] source, output logic [3:0] hi, "
            "output logic out); always_comb begin "
            "{>>2 {hi, out}} = source; end endmodule")
        statement = envelope["design"]["modules"][0]["processes"][0]["body"]["stmts"][0]
        self.assertEqual(statement["kind"], "Unsupported")

    def test_continuous_right_streaming_accepts_fixed_array_cell(self):
        envelope = self.extract(
            "module top(input logic [4:0] source, output logic [3:0] hi, "
            "output logic out); logic [3:0] arr [0:1]; "
            "assign {>>{arr[0], out}} = source; assign hi = arr[0]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        target = processes[0]["target"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual(target["kind"], "ConcatTarget")
        self.assertEqual([part["name"] for part in target["parts"]],
                         ["arr[0]", "out"])

    def test_continuous_right_streaming_accepts_cell_slice(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output logic [1:0] out); "
            "logic [3:0] arr [0:1]; assign {>>{arr[0][3:2], out}} = source; "
            "endmodule")
        target = envelope["design"]["modules"][0]["processes"][0]["target"]
        self.assertEqual(target["kind"], "ConcatTarget")
        self.assertEqual(target["parts"][0]["kind"], "PartSel")

    def test_right_streaming_wider_source_keeps_leading_bits(self):
        for assignment in ("assign", "always_comb"):
            with self.subTest(assignment=assignment):
                envelope = self.extract(
                    "module top(input logic [11:0] source, "
                    "output logic [3:0] hi, lo); " + assignment +
                    " {>> {hi, lo}} = source; endmodule")
                process, = envelope["design"]["modules"][0]["processes"]
                statement = process if assignment == "assign" else process["body"]
                value = statement["value"]
                self.assertEqual(value["kind"], "PartSel")
                self.assertEqual(value["width"], 8)
                self.assertEqual((value["msb"]["value"], value["lsb"]["value"]),
                                 (11, 4))

    def test_continuous_right_streaming_accepts_nested_union_leaves(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output logic [1:0] out); "
            "struct packed { union packed { logic [1:0] all; "
            "logic [1:0] alt; } inner; logic [1:0] tail; } value; "
            "assign {>>{value.inner.all, value.tail}} = source; "
            "assign out = value.inner.alt; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual([process["kind"] for process in processes],
                         ["Assign", "Assign"])
        target = processes[0]["target"]
        self.assertEqual(target["kind"], "ConcatTarget")
        self.assertEqual([part["kind"] for part in target["parts"]],
                         ["PartSel", "PartSel"])
        self.assertEqual(target["width"], 4)
        self.assertEqual(processes[1]["value"]["kind"], "PartSel")

    def test_continuous_right_streaming_nested_union_alias_overlap_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output logic [1:0] out); "
            "struct packed { union packed { logic [1:0] all; "
            "logic [1:0] alt; } inner; logic [1:0] tail; } value; "
            "assign {>>{value.inner.all, value.inner.alt}} = source; "
            "assign out = value.inner.all; endmodule")
        process = envelope["design"]["modules"][0]["processes"][0]
        self.assertEqual(process["kind"], "Unsupported")
        self.assertEqual(process["sv_kind"], "AssignmentExpression:target")

    def test_continuous_right_streaming_dynamic_nested_union_leaf_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [2:0] source, input logic index, "
            "output logic out); struct packed { union packed { logic [1:0] all; "
            "logic [1:0] alt; } inner; } value; "
            "assign {>>{value.inner.alt[index], out}} = source; endmodule")
        process = envelope["design"]["modules"][0]["processes"][0]
        self.assertEqual(process["kind"], "Unsupported")


if __name__ == "__main__":
    unittest.main()
