"""Fixed integral unpacked ports flatten to the existing scalar port cells."""
import json
import tempfile
import unittest
from pathlib import Path

import extract


def find(node, pred, found=None):
    found = [] if found is None else found
    if isinstance(node, dict):
        if pred(node):
            found.append(node)
        for value in node.values():
            find(value, pred, found)
    elif isinstance(node, list):
        for value in node:
            find(value, pred, found)
    return found


class SymbolicUnpackedPorts(unittest.TestCase):
    def extract(self, source):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            return json.loads(out.read_text())["design"]["modules"][0]

    def test_fixed_integral_ports_flatten_to_cells(self):
        module = self.extract(
            "module top(input logic [3:0] a [0:1], "
            "output logic [3:0] y [0:1]); "
            "assign y[0] = a[0]; assign y[1] = ~a[1]; endmodule")
        self.assertEqual([p["name"] for p in module["ports"]],
                         ["a[0]", "a[1]", "y[0]", "y[1]"])
        self.assertEqual([p["kind"] for p in module["ports"]],
                         ["Port"] * 4)
        self.assertEqual([p["target"]["name"] for p in module["processes"]],
                         ["y[0]", "y[1]"])

    def test_nested_and_signed_array_ports_flatten_to_cells(self):
        module = self.extract(
            "module top(input logic signed [3:0] a [0:1], "
            "input logic [3:0] grid [0:1][0:1], "
            "output logic y [0:1][0:1]); "
            "assign y[0][0] = a[0][0] ^ grid[0][0][0]; "
            "assign y[0][1] = grid[0][1][0]; "
            "assign y[1][0] = grid[1][0][0]; "
            "assign y[1][1] = grid[1][1][0]; endmodule")
        self.assertEqual(
            [p["name"] for p in module["ports"]],
            ["a[0]", "a[1]", "grid[0][0]", "grid[0][1]",
             "grid[1][0]", "grid[1][1]", "y[0][0]", "y[0][1]",
             "y[1][0]", "y[1][1]"])
        self.assertTrue(all(p["kind"] == "Port" for p in module["ports"]))
        self.assertTrue(all(p.get("signed") is True
                            for p in module["ports"][:2]))

    def test_parameter_dependent_nested_array_ports_retain_shape(self):
        module = self.extract(
            "module top #(parameter int N = 2) ("
            "input logic [3:0] grid [0:N-1][0:1], output logic y); "
            "assign y = grid[0][0][0]; endmodule")
        grid = next(p for p in module["ports"] if p["name"] == "grid")
        self.assertEqual(grid["kind"], "UnpackedDecl")
        self.assertEqual(len(grid["unpacked"]), 2)
        self.assertEqual(grid["unpacked"][0]["lsb"]["kind"], "Binary")

    def test_partial_fixed_output_net_array_ports_flatten_with_z_cell(self):
        module = self.extract(
            "module top(input logic a, output wire logic [3:0] y [0:1]); "
            "assign y[0] = {4{a}}; endmodule")
        ports = module["ports"]
        self.assertEqual([p["name"] for p in ports], ["a", "y[0]", "y[1]"])
        self.assertEqual(ports[2]["init"]["bits"], "zzzz")

    def test_multi_driver_output_net_array_ports_stay_loud(self):
        module = self.extract(
            "module top(input logic a, output wire logic [3:0] y [0:1]); "
            "assign y[0] = {4{a}}; assign y[0] = 4'h0; endmodule")
        kinds = [n["sv_kind"] for n in find(
            module, lambda n: n.get("kind") == "Unsupported")]
        self.assertIn("PortSymbol:type", kinds)

    def test_fixed_input_net_array_ports_flatten_to_cells(self):
        module = self.extract(
            "module top(input wire logic [3:0] a [0:1], "
            "output logic [3:0] y); assign y = a[0] ^ a[1]; endmodule")
        self.assertEqual([p["name"] for p in module["ports"]],
                         ["a[0]", "a[1]", "y"])
        self.assertTrue(all(p["kind"] == "Port" for p in module["ports"]))

    def test_fixed_output_net_array_with_one_driver_per_cell_flattens(self):
        module = self.extract(
            "module top(input logic [3:0] a, output wire logic [3:0] y [0:1]);"
            " assign y[0] = a; assign y[1] = ~a; endmodule")
        self.assertEqual([p["name"] for p in module["ports"]],
                         ["a", "y[0]", "y[1]"])
        self.assertTrue(all(p["kind"] == "Port" for p in module["ports"]))

    def test_fixed_internal_wire_array_with_one_driver_per_cell_flattens(self):
        module = self.extract(
            "module top(input logic [3:0] a, output logic [3:0] y);"
            " wire logic [3:0] mem [0:1];"
            " assign mem[0] = a; assign mem[1] = ~a;"
            " assign y = mem[0] ^ mem[1]; endmodule")
        cells = [d for d in module["decls"] if d.get("kind") == "Var"]
        self.assertEqual([d["name"] for d in cells], ["mem[0]", "mem[1]"])
        self.assertTrue(all(d.get("net_as_variable") for d in cells))

    def test_fixed_signed_array_variable_preserves_signed_metadata(self):
        module = self.extract(
            "module top(input logic signed [3:0] a, output logic signed [3:0] y);"
            " logic signed [3:0] arr [0:1]; assign arr[0] = a;"
            " assign arr[1] = -a; assign y = arr[0] + 4'sd1; endmodule")
        cells = [d for d in module["decls"] if d.get("kind") == "Var"]
        self.assertEqual([d["name"] for d in cells], ["arr[0]", "arr[1]"])
        self.assertTrue(all(d.get("signed") is True for d in cells))

    def test_fixed_signed_array_ports_flatten_with_signed_metadata(self):
        module = self.extract(
            "module top(input logic signed [3:0] a [0:1], "
            "output logic signed [3:0] y [0:1]); "
            "assign y[0] = a[0] + 4'sd1; "
            "assign y[1] = -a[1]; endmodule")
        ports = module["ports"]
        self.assertEqual([p["name"] for p in ports],
                         ["a[0]", "a[1]", "y[0]", "y[1]"])
        self.assertTrue(all(p.get("signed") is True for p in ports))


if __name__ == "__main__":
    unittest.main()
