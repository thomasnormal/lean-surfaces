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

    def test_multiple_selected_drivers_stay_on_continuous_boundary(self):
        design = extract_source(
            "module top; wire [1:0] bus; assign bus[0] = 1'b1; "
            "assign bus[1] = 1'b0; endmodule")
        processes = design["modules"][0]["processes"]
        self.assertEqual([process["kind"] for process in processes],
                         ["Assign", "Assign"])

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


if __name__ == "__main__":
    unittest.main()
