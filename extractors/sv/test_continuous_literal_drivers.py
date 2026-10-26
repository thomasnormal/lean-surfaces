"""Literal continuous net drivers lower only when the driver is unique."""
import unittest

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

import extract


def extract_source(source):
    tree = SyntaxTree.fromText(source)
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    extract._SOURCE_BYTES = source.encode()
    return extract.convert_design(tree.sourceManager, compilation)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from nodes(child)


class ContinuousLiteralDrivers(unittest.TestCase):
    def test_constant_bit_driver_lowers_to_time_zero_selected_write(self):
        design = extract_source(
            "module top; wire [3:0] bus; assign bus[2] = 1'b1; "
            "initial if (bus[2] === 1'b1) $display(\"PASS\"); endmodule")
        process = design["modules"][0]["processes"][0]
        self.assertEqual(process["kind"], "Initial")
        assignment = process["body"]
        self.assertEqual(assignment["kind"], "BlockingAssign")
        self.assertEqual(assignment["target"]["kind"], "SelectTarget")
        self.assertTrue(process.get("continuous_constant_lowered"))

    def test_multiple_disjoint_selected_literal_drivers_lower(self):
        design = extract_source(
            "module top; wire [3:0] bus; assign bus[1:0] = 2'b01; "
            "assign bus[3:2] = 2'b10; endmodule")
        processes = design["modules"][0]["processes"]
        self.assertEqual([process["kind"] for process in processes],
                         ["Initial", "Initial"])
        self.assertTrue(all(process.get("continuous_selected_static_resolution")
                             for process in processes))
        self.assertEqual(processes[0]["body"]["value"]["bits"], "1001")

    def test_overlapping_selected_literal_drivers_resolve_at_time_zero(self):
        design = extract_source(
            "module top; wire [3:0] bus; assign bus[2:0] = 3'b101; "
            "assign bus[3:1] = 3'b100; endmodule")
        processes = design["modules"][0]["processes"]
        self.assertEqual([process["kind"] for process in processes],
                         ["Initial", "Initial"])
        self.assertTrue(all(process.get("continuous_selected_static_resolution")
                             for process in processes))
        self.assertEqual(processes[0]["body"]["value"]["bits"], "1x01")

    def test_literal_fixed_array_variable_cells_lower_to_time_zero_writes(self):
        design = extract_source(
            "module top; logic [3:0] cells [0:1]; "
            "assign cells[0] = 4'ha; assign cells[1] = 4'h5; endmodule")
        processes = design["modules"][0]["processes"]
        self.assertEqual([process["kind"] for process in processes],
                         ["Initial", "Initial"])
        self.assertTrue(all(process.get("continuous_array_cell_lowered")
                             for process in processes))
        self.assertEqual(
            [process["body"]["target"]["name"] for process in processes],
            ["cells[0]", "cells[1]"])

    def test_literal_fixed_array_net_cells_lower_to_time_zero_writes(self):
        design = extract_source(
            "module top; wire [3:0] cells [0:1]; "
            "assign cells[0] = 4'ha; assign cells[1] = 4'h5; endmodule")
        module = design["modules"][0]
        self.assertEqual(
            [(decl["kind"], decl["name"]) for decl in module["decls"]],
            [("Net", "cells[0]"), ("Net", "cells[1]")])
        processes = module["processes"]
        self.assertEqual([process["kind"] for process in processes],
                         ["Initial", "Initial"])
        self.assertTrue(all(process.get("continuous_array_cell_lowered")
                             for process in processes))

    def test_literal_packed_variable_drivers_lower_to_time_zero_writes(self):
        design = extract_source(
            "module top; logic [3:0] whole, window; "
            "assign whole = 4'ha; assign window[2:1] = 2'b01; endmodule")
        processes = design["modules"][0]["processes"]
        self.assertEqual([process["kind"] for process in processes],
                         ["Initial", "Initial"])
        self.assertTrue(all(process.get("continuous_constant_lowered")
                             for process in processes))
        self.assertEqual(processes[1]["body"]["target"]["kind"],
                         "SelectTarget")

    def test_multiple_literal_wire_drivers_resolve_at_time_zero(self):
        design = extract_source(
            "module top; wire conflict, agree, z_only, unknown; "
            "assign conflict = 1'b0; assign conflict = 1'b1; "
            "assign agree = 1'b1; assign agree = 1'b1; "
            "assign z_only = 1'bz; assign z_only = 1'bz; "
            "assign unknown = 1'bx; assign unknown = 1'b0; endmodule")
        initial = [process for process in design["modules"][0]["processes"]
                   if process.get("continuous_static_resolution")]
        self.assertEqual(len(initial), 8)
        values = {
            process["body"]["target"]["name"]:
            process["body"]["value"]["bits"]
            for process in initial
            if process["body"]["kind"] == "BlockingAssign"
        }
        self.assertEqual(values,
                         {"conflict": "x", "agree": "1",
                          "z_only": "z", "unknown": "x"})

    def test_single_literal_initial_write_sources_resolve(self):
        design = extract_source(
            "module top; logic a, b; wire y, z; "
            "assign y = a; assign z = b; "
            "initial begin a = 1'b1; b = 1'b1; "
            "if (y === 1'b1 && z === 1'b1) $display(\"PASS\"); "
            "end endmodule")
        module = design["modules"][0]
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        initial = [process for process in module["processes"]
                   if process.get("continuous_constant_lowered")]
        self.assertEqual(len(initial), 2)
        values = [process["body"].get("value", {}).get("bits")
                  for process in initial if process["body"]["kind"] == "BlockingAssign"]
        self.assertIn("1", values)

    def test_multiple_initial_writes_remain_dynamic(self):
        design = extract_source(
            "module top; logic source; wire bus; assign bus = source; "
            "initial begin source = 1'b0; source = 1'b1; end endmodule")
        self.assertTrue(any(node.get("kind") == "Assign"
                            for node in nodes(design)))
        self.assertFalse(any(node.get("continuous_static_resolution")
                             for node in nodes(design)))

    def test_selected_single_initial_write_sources_resolve(self):
        design = extract_source(
            "module top; logic [7:0] source; wire [7:0] bus; "
            "assign bus[0] = source[0]; assign bus[3:0] = source[3:0]; "
            "initial source = 8'b1010_1010; endmodule")
        module = design["modules"][0]
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             for node in nodes(design)))
        initial = [process for process in module["processes"]
                   if process.get("continuous_selected_static_resolution")]
        self.assertEqual(len(initial), 2)
        self.assertEqual(initial[0]["body"]["value"]["bits"], "zzzz1010")
        self.assertEqual(initial[1]["body"]["kind"], "Empty")

    def test_selected_declaration_literal_source_resolves(self):
        design = extract_source(
            "module top; logic [7:0] source = 8'b1010_1010; "
            "wire [7:0] bus; assign bus[0] = source[0]; "
            "assign bus[3:0] = source[3:0]; endmodule")
        initial = [process for process in design["modules"][0]["processes"]
                   if process.get("continuous_selected_static_resolution")]
        self.assertEqual(len(initial), 2)
        self.assertEqual(initial[0]["body"]["value"]["bits"], "zzzz1010")

    def test_selected_multiple_initial_writes_remain_dynamic(self):
        design = extract_source(
            "module top; logic [3:0] source; wire [3:0] bus; "
            "assign bus[1:0] = source[1:0]; "
            "initial begin source = 4'b0001; source = 4'b0010; end endmodule")
        self.assertTrue(any(node.get("kind") == "Assign"
                            for node in nodes(design)))
        self.assertFalse(any(node.get("continuous_selected_static_resolution")
                             for node in nodes(design)))

    def test_control_dependent_initial_write_remains_dynamic(self):
        design = extract_source(
            "module top; logic source; wire bus; assign bus = source; "
            "initial if (1'b1) source = 1'b1; endmodule")
        self.assertTrue(any(node.get("kind") == "Assign"
                            for node in nodes(design)))
        self.assertFalse(any(node.get("continuous_static_resolution")
                             for node in nodes(design)))

    def test_literal_tri_driver_uses_flat_net_path(self):
        design = extract_source(
            "module top; tri bus; assign bus = 1'b1; endmodule")
        module = design["modules"][0]
        self.assertEqual(module["decls"][0]["kind"], "Net")
        self.assertEqual(module["decls"][0]["name"], "bus")
        self.assertEqual([process["kind"] for process in module["processes"]],
                         ["Initial"])
        self.assertTrue(module["processes"][0].get("continuous_constant_lowered"))

    def test_wand_literal_drivers_use_wired_and_resolution(self):
        design = extract_source(
            "module top; wand bus; assign bus = 1'b1; "
            "assign bus = 1'b0; endmodule")
        module = design["modules"][0]
        self.assertEqual(module["decls"][0].get("continuous_resolution"), "and")
        initial = [p for p in module["processes"]
                   if p.get("continuous_static_resolution")]
        self.assertEqual(initial[0]["body"]["value"]["bits"], "0")

    def test_wor_literal_drivers_use_wired_or_resolution(self):
        design = extract_source(
            "module top; wor bus; assign bus = 1'b0; "
            "assign bus = 1'b1; endmodule")
        module = design["modules"][0]
        self.assertEqual(module["decls"][0].get("continuous_resolution"), "or")
        initial = [p for p in module["processes"]
                   if p.get("continuous_static_resolution")]
        self.assertEqual(initial[0]["body"]["value"]["bits"], "1")

    def test_wand_dynamic_driver_stays_loud(self):
        design = extract_source(
            "module top; wand bus; logic source; assign bus = source; "
            "assign bus = 1'b1; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "NetSymbol:WAnd"
                            for node in nodes(design)))

    def test_dynamic_tri_driver_stays_loud(self):
        design = extract_source(
            "module top; tri bus; logic source; assign bus = source; endmodule")
        self.assertEqual(design["modules"][0]["decls"][0]["kind"],
                         "Unsupported")
        self.assertEqual(design["modules"][0]["decls"][0]["sv_kind"],
                         "NetSymbol:Tri")

    def test_single_strength_literal_driver_lowers(self):
        design = extract_source(
            "module top; wire bus; "
            "assign (strong1, strong0) bus = 1'b1; endmodule")
        processes = design["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Initial")
        self.assertTrue(processes[0].get("continuous_strength"))

    def test_multiple_strength_literal_drivers_stay_loud(self):
        design = extract_source(
            "module top; wire bus; "
            "assign (strong1, strong0) bus = 1'b1; "
            "assign (pull1, pull0) bus = 1'b0; endmodule")
        process = design["modules"][0]["processes"][0]
        self.assertEqual(process["kind"], "Assign")
        self.assertTrue(process.get("continuous_strength"))

    def test_single_strength_tri_literal_driver_lowers(self):
        design = extract_source(
            "module top; tri bus; "
            "assign (strong1, strong0) bus = 1'b1; endmodule")
        processes = design["modules"][0]["processes"]
        self.assertEqual(processes[0]["kind"], "Initial")
        self.assertTrue(processes[0].get("continuous_strength"))

    def test_multiple_tri_strength_drivers_stay_loud(self):
        design = extract_source(
            "module top; tri bus; "
            "assign (strong1, strong0) bus = 1'b1; "
            "assign (pull1, pull0) bus = 1'b0; endmodule")
        self.assertTrue(any(node.get("kind") == "Unsupported"
                            and node.get("sv_kind") == "NetSymbol:Tri"
                            for node in nodes(design)))

    def test_single_strength_packed_select_lowers(self):
        design = extract_source(
            "module top; wire [3:0] bus; "
            "assign (strong1, strong0) bus[2] = 1'b1; endmodule")
        process = design["modules"][0]["processes"][0]
        self.assertEqual(process["kind"], "Initial")
        self.assertEqual(process["body"]["target"]["kind"], "SelectTarget")
        self.assertTrue(process.get("continuous_strength"))

    def test_multiple_strength_packed_select_drivers_stay_loud(self):
        design = extract_source(
            "module top; wire [3:0] bus; "
            "assign (strong1, strong0) bus[2] = 1'b1; "
            "assign (pull1, pull0) bus[2] = 1'b0; endmodule")
        process = design["modules"][0]["processes"][0]
        self.assertEqual(process["kind"], "Assign")
        self.assertTrue(process.get("continuous_strength"))

    def test_dynamic_array_element_continuous_target_is_rejected_inertly(self):
        design = extract_source(
            'module top; int dyn[]; assign dyn[0] = 1; '
            'initial begin $display("PASS"); $finish; end endmodule')
        module = design["modules"][0]
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             and node.get("sv_kind") ==
                             "AssignmentExpression:target"
                             for node in nodes(design)))
        rejected = [process for process in module["processes"]
                    if process.get("dynamic_array_continuous_target_rejected")]
        self.assertEqual(len(rejected), 1)
        self.assertEqual(rejected[0]["body"]["kind"], "Empty")

    def test_multiple_variable_continuous_drivers_are_rejected_inertly(self):
        design = extract_source(
            'module top; logic a, b, value; assign value = a; '
            'assign value = b; initial $display("PASS"); endmodule')
        module = design["modules"][0]
        self.assertFalse(any(node.get("kind") == "Unsupported"
                             and node.get("sv_kind") ==
                             "AssignmentExpression:target"
                             for node in nodes(design)))
        rejected = [process for process in module["processes"]
                    if process.get("multiple_variable_continuous_drivers_rejected")]
        self.assertEqual(len(rejected), 2)
        self.assertTrue(all(process["body"]["kind"] == "Empty"
                            for process in rejected))


if __name__ == "__main__":
    unittest.main()
