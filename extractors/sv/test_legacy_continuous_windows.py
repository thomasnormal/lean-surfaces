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

    def test_nested_fixed_array_cells_flatten_in_source_order(self):
        envelope = self.extract(
            "module top; bit [3:0] value [2][3]; "
            "initial begin value[1][2] = 4'ha; end endmodule")
        decls = envelope["design"]["modules"][0]["decls"]
        self.assertEqual([d["name"] for d in decls], [
            "value[0][0]", "value[0][1]", "value[0][2]",
            "value[1][0]", "value[1][1]", "value[1][2]",
        ])
        stmt = envelope["design"]["modules"][0]["processes"][0]["body"]["stmts"][0]
        self.assertEqual(stmt["target"]["name"], "value[1][2]")

    def test_nested_fixed_array_pattern_initializes_flattened_two_state_cells(self):
        envelope = self.extract(
            "module top; int value [1:2][1:3] = '{2\n"
            "  {'{3{5}}}; initial begin $display(\"%0d\", value[2][3]); "
            "$finish; end endmodule")
        decls = envelope["design"]["modules"][0]["decls"]
        self.assertEqual([d["name"] for d in decls], [
            "value[1][1]", "value[1][2]", "value[1][3]",
            "value[2][1]", "value[2][2]", "value[2][3]"])
        self.assertTrue(all(d["init"]["kind"] == "Squash2" for d in decls))
        self.assertTrue(all(d["init"]["operand"]["bits"] == "0" * 29 + "101"
                            for d in decls))

    def test_nested_unpacked_cells_accept_multidimensional_packed_leaf(self):
        envelope = self.extract(
            "module top; bit [1:0][3:0] value [0:1]; "
            "initial begin value[0] = 8'hA5; end endmodule")
        decls = envelope["design"]["modules"][0]["decls"]
        self.assertEqual([(d["name"], d["width"]) for d in decls],
                         [("value[0]", 8), ("value[1]", 8)])
        self.assertEqual(decls[0]["init"]["bits"], "0" * 8)

    def test_unpacked_struct_integral_fields_flatten_to_cells(self):
        envelope = self.extract(
            "module top; typedef struct { int count; bit [7:0] mask; } item_t; "
            "item_t item; initial begin item.count = 3; item.mask = 5; "
            "item.count += 4; item.mask <<= 1; end endmodule")
        decls = envelope["design"]["modules"][0]["decls"]
        self.assertEqual([d["name"] for d in decls],
                         ["item.count", "item.mask"])
        stmts = envelope["design"]["modules"][0]["processes"][0]["body"]["stmts"]
        self.assertEqual([s["kind"] for s in stmts],
                         ["BlockingAssign", "BlockingAssign",
                          "BlockingAssign", "BlockingAssign"])
        self.assertEqual(stmts[2]["target"]["name"], "item.count")
        self.assertEqual(stmts[3]["target"]["name"], "item.mask")

    def test_unpacked_array_concat_initializer_flattens_source_arrays(self):
        envelope = self.extract(
            "module top; typedef int triple_t [0:2]; "
            "typedef int nine_t [0:8]; initial begin "
            "triple_t prefix = '{1, 2, 3}; "
            "nine_t values = {prefix, 4, triple_t'{5, 6, 7}, 8, 9}; "
            "$display(\"%0d\", values[8]); $finish; end endmodule")
        decls = envelope["design"]["modules"][0]["decls"]
        values = [d for d in decls if "values[" in d.get("name", "")]
        self.assertEqual(len(values), 9)
        self.assertEqual(values[0]["init"]["operand"]["bits"], "0" * 31 + "1")
        self.assertEqual(values[-1]["init"]["operand"]["bits"], "0" * 28 + "1001")
        self.assertFalse(any(n.get("kind") == "Unsupported"
                             for n in self._walk(envelope)))

    def test_unpacked_array_concat_initializer_rejects_runtime_source(self):
        envelope = self.extract(
            "module top; typedef int pair_t [0:1]; pair_t source; "
            "pair_t value = {source, 3}; endmodule")
        self.assertTrue(any(n.get("kind") == "Unsupported"
                            and n.get("sv_kind") == "VariableSymbol:2state"
                            for n in self._walk(envelope)))

    def test_fixed_array_of_unpacked_integral_structs_flattens_fields(self):
        envelope = self.extract(
            "module top; typedef struct { bit [3:0] x; int y; } S; "
            "S value [0:1]; initial begin value[0].x = 4'ha; "
            "value[1].y = 3; end endmodule")
        decls = envelope["design"]["modules"][0]["decls"]
        self.assertEqual([d["name"] for d in decls],
                         ["value[0].x", "value[0].y", "value[1].x", "value[1].y"])
        stmts = envelope["design"]["modules"][0]["processes"][0]["body"]["stmts"]
        self.assertEqual([s["target"]["name"] for s in stmts],
                         ["value[0].x", "value[1].y"])

    def test_fixed_array_of_unpacked_struct_aggregate_initializer_stays_loud(self):
        envelope = self.extract(
            "module top; typedef struct { bit [3:0] x; int y; } S; "
            "S value [0:1] = '{'{4'ha, 1}, '{4'hb, 2}}; endmodule")
        self.assertTrue(any(n.get("kind") == "Unsupported"
                            and n.get("sv_kind") == "VariableSymbol:2state"
                            for n in self._walk(envelope)))

    def test_nested_unpacked_integral_struct_fields_flatten_recursively(self):
        envelope = self.extract(
            "module top; struct { int a; struct { bit [3:0] b; bit c; } inner; } value; "
            "initial begin value.a = 3; value.inner.b = 4'ha; value.inner.c = 1; end")
        decls = envelope["design"]["modules"][0]["decls"]
        self.assertEqual([d["name"] for d in decls],
                         ["value.a", "value.inner.b", "value.inner.c"])
        stmts = envelope["design"]["modules"][0]["processes"][0]["body"]["stmts"]
        self.assertEqual([s["target"]["name"] for s in stmts],
                         ["value.a", "value.inner.b", "value.inner.c"])

    def test_module_event_declaration_is_inert_on_time_zero_path(self):
        envelope = self.extract(
            "module top; event named_ev; initial begin $display(\"PASS\"); "
            "$finish; end endmodule")
        module = envelope["design"]["modules"][0]
        self.assertEqual(module["decls"], [])
        self.assertEqual(module["others"], [])

    def test_module_event_wait_remains_loud(self):
        envelope = self.extract(
            "module top; event named_ev; initial begin @named_ev; end endmodule")
        module = envelope["design"]["modules"][0]
        self.assertTrue(any(item.get("kind") == "Unsupported"
                            for item in module["processes"][0]["body"]["stmts"]))

    def test_module_real_declaration_is_inert_on_time_zero_path(self):
        envelope = self.extract(
            "module top; real rr; initial begin $display(\"PASS\"); "
            "$finish; end endmodule")
        module = envelope["design"]["modules"][0]
        self.assertEqual(module["decls"], [])
        self.assertEqual(module["others"], [])

    def test_module_real_read_remains_loud(self):
        envelope = self.extract(
            "module top; real rr; initial begin if (rr == 0) $display(\"PASS\"); "
            "end endmodule")
        self.assertTrue(any(item.get("kind") == "Unsupported"
                            for item in self._walk(envelope)))

    @staticmethod
    def _walk(value):
        if isinstance(value, dict):
            yield value
            for child in value.values():
                yield from LegacyContinuousWindows._walk(child)
        elif isinstance(value, list):
            for child in value:
                yield from LegacyContinuousWindows._walk(child)

    def test_fixed_array_out_of_bounds_write_is_empty(self):
        envelope = self.extract(
            "module top; int value [0:3]; "
            "initial begin value[99] = 7; end endmodule")
        stmt = envelope["design"]["modules"][0]["processes"][0]["body"]["stmts"][0]
        self.assertEqual(stmt["kind"], "Empty")
        self.assertTrue(stmt["oob_write_noop"])

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

    def test_noncanonical_indexed_direct_windows_normalize(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [1:0] out); "
            "logic [10:7] value; assign value[8 +: 2] = source; "
            "assign out = value[9 -: 2]; endmodule")
        target, readback = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(target["target"]["kind"], "SelectTarget")
        self.assertEqual(target["target"]["index"]["bits"],
                         "0" * 31 + "1")
        self.assertFalse(target["target"]["descending"])
        self.assertEqual(readback["value"]["kind"], "SelectRead")
        self.assertEqual(readback["value"]["index"]["bits"],
                         "0" * 30 + "10")
        self.assertTrue(readback["value"]["descending"])

    def test_noncanonical_indexed_nested_member_windows_normalize(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [1:0] out); "
            "struct packed { logic [10:7] hi; logic [1:0] lo; } value; "
            "assign value.hi[8 +: 2] = source; "
            "assign out = value.hi[9 -: 2]; endmodule")
        target, readback = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(target["target"]["kind"], "SelectTarget")
        self.assertEqual(target["target"]["value"]["name"], "value")
        self.assertEqual(target["target"]["index"]["bits"],
                         "0" * 30 + "11")
        self.assertFalse(target["target"]["descending"])
        self.assertEqual(readback["value"]["kind"], "SelectRead")
        self.assertEqual(readback["value"]["index"]["bits"],
                         "0" * 29 + "100")
        self.assertTrue(readback["value"]["descending"])

    def test_noncanonical_indexed_fixed_array_cell_windows_normalize(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [1:0] out); "
            "logic [10:7] value [0:0]; "
            "assign value[0][8 +: 2] = source; "
            "assign out = value[0][9 -: 2]; endmodule")
        target, readback = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(target["target"]["kind"], "SelectTarget")
        self.assertEqual(target["target"]["value"]["name"], "value[0]")
        self.assertEqual(target["target"]["index"]["bits"],
                         "0" * 31 + "1")
        self.assertFalse(target["target"]["descending"])
        self.assertEqual(readback["value"]["kind"], "SelectRead")
        self.assertEqual(readback["value"]["index"]["bits"],
                         "0" * 30 + "10")
        self.assertTrue(readback["value"]["descending"])

    def test_noncanonical_indexed_dynamic_effectful_and_out_of_range_stay_loud(self):
        prefix = (
            "module top(input logic [1:0] source, input logic [3:0] index, "
            "output logic [1:0] out); logic [10:7] value; ")
        dynamic = self.extract(
            prefix +
            "assign value[index +: 2] = source; assign out = value[9 -: 2]; "
            "endmodule")
        self.assertEqual(dynamic["design"]["modules"][0]["processes"][0]["kind"],
                         "Unsupported")
        effectful = self.extract(
            prefix +
            "assign value[index++ +: 2] = source; assign out = value[9 -: 2]; "
            "endmodule")
        self.assertEqual(effectful["design"]["modules"][0]["processes"][0]["kind"],
                         "Unsupported")
        out_of_range = self.extract(
            "module top(input logic [1:0] source, output logic [1:0] out); "
            "logic [10:7] value; assign value[10 +: 2] = source; "
            "assign out = value[7 -: 2]; endmodule")
        self.assertEqual(
            out_of_range["design"]["modules"][0]["processes"][0]["kind"],
            "Unsupported")

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

    def test_nested_packed_member_indexed_selection_keeps_direction(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [1:0] out); "
            "struct packed { struct packed { logic [3:0] hi; "
            "logic [1:0] lo; } inner; } value; "
            "assign value.inner.hi[1 +: 2] = source; "
            "assign out = value.inner.hi[3 -: 2]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        target, readback = processes
        self.assertEqual(target["target"]["index"]["bits"],
                         "0" * 30 + "11")
        self.assertFalse(target["target"]["descending"])
        self.assertEqual(readback["value"]["index"]["bits"],
                         "0" * 29 + "101")
        self.assertTrue(readback["value"]["descending"])

    def test_dynamic_nested_member_selection_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, input logic [2:0] index, "
            "output logic out); struct packed { logic [3:0] hi; "
            "logic [1:0] lo; } value; assign value.hi[index] = source[0]; "
            "assign out = value.hi[0]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Unsupported")

    def test_nested_packed_union_member_windows_alias_flat_vector(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [1:0] out); "
            "struct packed { union packed { logic [3:0] all; "
            "logic [3:0] alt; } inner; } value; "
            "assign value.inner.alt[1 +: 2] = source; "
            "assign out = value.inner.all[1 +: 2]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        target, readback = processes
        self.assertEqual(target["kind"], "Assign")
        self.assertEqual(target["target"]["kind"], "SelectTarget")
        self.assertEqual(target["target"]["value"]["name"], "value")
        self.assertEqual(readback["value"]["kind"], "SelectRead")
        self.assertEqual(readback["value"]["value"]["name"], "value")
        self.assertEqual(target["target"]["index"]["bits"],
                         readback["value"]["index"]["bits"])

    def test_nested_packed_union_overlapping_alias_windows_stay_loud(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [3:0] out); "
            "struct packed { union packed { logic [3:0] all; "
            "logic [3:0] alt; } inner; } value; "
            "assign value.inner.all[3:2] = source; "
            "assign value.inner.alt[3:2] = source; "
            "assign out = value.inner.all; endmodule")
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

    def test_direct_packed_union_alias_windows_are_continuous(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [1:0] out); "
            "union packed { logic [3:0] bytes; logic [3:0] alt; } value; "
            "assign value.bytes[1 +: 2] = source; "
            "assign out = value.alt[3 -: 2]; endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        target, readback = processes
        self.assertEqual(target["target"]["kind"], "SelectTarget")
        self.assertEqual(target["target"]["value"]["name"], "value")
        self.assertEqual(target["target"]["index"]["bits"],
                         "0" * 31 + "1")
        self.assertEqual(readback["value"]["kind"], "SelectRead")
        self.assertEqual(readback["value"]["value"]["name"], "value")
        self.assertTrue(readback["value"]["descending"])

    def test_overlapping_packed_union_alias_windows_are_loud(self):
        envelope = self.extract(
            "module top(input logic [1:0] source, output logic [3:0] out); "
            "union packed { logic [3:0] bytes; logic [3:0] alt; } value; "
            "assign value.bytes[3:2] = source; "
            "assign value.alt[3:2] = source; assign out = value.alt; "
            "endmodule")
        processes = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Assign")
        self.assertEqual(processes[1]["kind"], "Unsupported")
        self.assertEqual(processes[1]["sv_kind"],
                         "AssignmentExpression:target")

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
        process = envelope["design"]["modules"][0]["processes"][0]
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

    def test_right_streaming_nested_union_member_is_a_continuous_leaf(self):
        envelope = self.extract(
            "module top(input logic [2:0] source, output logic out); "
            "struct packed { union packed { logic [1:0] all; "
            "logic [1:0] alt; } inner; } value; "
            "assign {>>{value.inner.alt, out}} = source; endmodule")
        process, = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(process["kind"], "Assign")
        self.assertEqual(process["target"]["kind"], "ConcatTarget")
        leaf = process["target"]["parts"][0]
        self.assertEqual(leaf["kind"], "SelectTarget")
        self.assertEqual(leaf["value"]["name"], "value")

    def test_right_streaming_nested_union_alias_overlap_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [3:0] source, output logic [1:0] out); "
            "struct packed { union packed { logic [1:0] all; "
            "logic [1:0] alt; } inner; } value; "
            "assign {>>{value.inner.all, value.inner.alt}} = source; "
            "assign out = value.inner.all; endmodule")
        process = envelope["design"]["modules"][0]["processes"][0]
        self.assertEqual(process["kind"], "Unsupported")
        self.assertEqual(process["sv_kind"], "AssignmentExpression:target")

    def test_right_streaming_dynamic_nested_union_member_stays_loud(self):
        envelope = self.extract(
            "module top(input logic [2:0] source, input logic [1:0] index, "
            "output logic out); struct packed { union packed { logic [1:0] all; "
            "logic [1:0] alt; } inner; } value; "
            "assign {>>{value.inner.alt[index], out}} = source; endmodule")
        process, = envelope["design"]["modules"][0]["processes"]
        self.assertEqual(process["kind"], "Unsupported")

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
