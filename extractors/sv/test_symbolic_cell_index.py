"""Unpacked-array cell indices that are default-point folds (sv-0.2,
2026-10-28, WP2 repair).

A fixed unpacked array is one declaration per cell in symbolic mode, and a
constant element select names its cell (`Ident "m[2]"`). slang elaborates a
module once, at its default parameters and at one iteration of each
generate loop, so the constant it reports for `m[i]` (genvar) or `m[K]`
(overridable parameter) is the DEFAULT point's: before this guard every
iteration read `m[0]` and every K wrote `m[0]`, silently. Such a select is
now refused (`ElementSelect:default-point-index`); literal and localparam
indices, and packed bit-selects with a genvar index inside a cell, keep
their encoding.
"""
import json
import tempfile
import unittest
from pathlib import Path

import extract

KIND = "ElementSelect:default-point-index"


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


def kinds(node):
    return [n["sv_kind"] for n in find(node, lambda n: n.get("kind") == "Unsupported")]


def idents(node):
    return sorted({n["name"] for n in find(node, lambda n: n.get("kind") == "Ident")})


class SymbolicCellIndex(unittest.TestCase):
    def extract(self, source, top="top"):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic(top, [str(src)], [], str(out))
            return json.loads(out.read_text())["design"]["modules"][0]

    CELLS = ("logic m [4]; assign m[0] = a[0]; assign m[1] = a[1];"
             " assign m[2] = a[2]; assign m[3] = a[3];")

    def test_genvar_read_is_refused(self):
        module = self.extract(
            "module top (input logic [3:0] a, output logic [3:0] y); " + self.CELLS +
            " for (genvar i = 0; i < 4; i++) begin : g assign y[i] = m[i]; end"
            " endmodule")
        self.assertIn(KIND, kinds(module))

    def test_parameter_read_is_refused(self):
        module = self.extract(
            "module top #(parameter int K = 0) (input logic [3:0] a, output logic y); "
            + self.CELLS + " assign y = m[K]; endmodule")
        self.assertEqual(kinds(module), [KIND])

    def test_parameter_continuous_write_is_refused(self):
        module = self.extract(
            "module top #(parameter int K = 0) (input logic a, output logic [3:0] y);"
            " logic m [4]; assign m[K] = a; assign y = {m[3], m[2], m[1], m[0]};"
            " endmodule")
        self.assertEqual(kinds(module), [KIND])

    def test_genvar_procedural_write_is_refused(self):
        module = self.extract(
            "module top (input logic clk, input logic [3:0] a, output logic [3:0] y);"
            " logic m [4];"
            " for (genvar i = 0; i < 4; i++) begin : g"
            " always_ff @(posedge clk) m[i] <= a[i]; end"
            " assign y = {m[3], m[2], m[1], m[0]}; endmodule")
        self.assertIn(KIND, kinds(module))

    def test_fixed_indices_keep_their_cells(self):
        module = self.extract(
            "module top #(parameter int W = 1) (input logic [3:0] a,"
            " output logic [3:0] y, output logic [W-1:0] z); localparam int L = 2;"
            " logic m [4]; assign m[0] = a[0]; assign m[1] = a[1];"
            " assign m[L] = a[2]; assign m[3] = a[3];"
            " assign y = {m[3], m[L], m[1], m[0]}; assign z = {W{m[0]}}; endmodule")
        self.assertEqual(kinds(module), [])
        self.assertTrue({"m[0]", "m[1]", "m[2]", "m[3]"} <= set(idents(module)))

    def test_genvar_bit_inside_a_cell_is_symbolic(self):
        module = self.extract(
            "module top (input logic [3:0] a, output logic [3:0] y);"
            " logic [3:0] m [2]; assign m[0] = a; assign m[1] = ~a;"
            " for (genvar i = 0; i < 4; i++) begin : g assign y[i] = m[0][i]; end"
            " endmodule")
        self.assertNotIn(KIND, kinds(module))
        self.assertIn("m[0]", idents(module))


if __name__ == "__main__":
    unittest.main()
