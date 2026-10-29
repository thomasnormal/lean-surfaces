"""Indexed part-selects in sv-0.2 symbolic mode.

`x[b +: w]` / `x[b -: w]` (and `x[hi:lo]`) whose base or bounds are
elaboration-time constants over parameters and genvars are `ArraySel` nodes
with symbolic labels (Lean resolves them per parameter point, out-of-range
bits included). A RUN-TIME base (one that reads a signal, IEEE 1800-2023
11.5.1) is an `ArraySel` too, on a 1-D vector with a descending range, in
READ positions only; its base is an ordinary value expression. A signed
run-time base is refused with its own kind.
"""
import json
import tempfile
import unittest
from pathlib import Path

import extract


def strip(node):
    if isinstance(node, dict):
        return {key: strip(value) for key, value in node.items()
                if key not in ("span", "resolved_width", "width")}
    if isinstance(node, list):
        return [strip(value) for value in node]
    return node


def kinds(node, found=None):
    found = [] if found is None else found
    if isinstance(node, dict):
        if "kind" in node:
            found.append(node["kind"])
        for value in node.values():
            kinds(value, found)
    elif isinstance(node, list):
        for value in node:
            kinds(value, found)
    return found


def sv_kinds(node, found=None):
    found = [] if found is None else found
    if isinstance(node, dict):
        if node.get("kind") == "Unsupported":
            found.append(node.get("sv_kind"))
        for value in node.values():
            sv_kinds(value, found)
    elif isinstance(node, list):
        for value in node:
            sv_kinds(value, found)
    return found


class SymbolicPartSelects(unittest.TestCase):
    def extract(self, source):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            return json.loads(out.read_text())["design"]["modules"][0]

    def test_parameter_bases_on_targets_and_reads(self):
        module = self.extract(
            "module top #(parameter int N = 4, parameter int W = 3)"
            " (input logic [N*W-1:0] a, output logic [N*W-1:0] y,"
            " output logic [N-1:0] z); genvar i;"
            " for (i = 0; i < N; i++) begin : g"
            " assign y[i*W +: W] = a[(N-1-i)*W +: W]; end"
            " assign z = a[(N-1)*W+N-1 -: N]; endmodule")
        self.assertNotIn("Unsupported", kinds(module))
        cell = strip(module["generates"][0]["body"][0])
        self.assertEqual(cell["target"]["kind"], "ArraySel")
        self.assertEqual(cell["target"]["part"]["mode"], "up")
        self.assertEqual(cell["target"]["part"]["right"],
                         {"kind": "ParamRef", "name": "W"})
        self.assertEqual(cell["value"]["kind"], "ArraySel")
        value = strip(module["processes"][0]["value"])
        self.assertEqual(value["kind"], "ArraySel")
        self.assertEqual(value["part"]["mode"], "down")
        self.assertEqual(value["part"]["right"], {"kind": "ParamRef", "name": "N"})

    def test_runtime_base_read_is_a_value_expression(self):
        module = self.extract(
            "module top #(parameter int W = 3) (input logic [7:0] v,"
            " input logic [2:0] sel, output logic [3:0] u, output logic [3:0] d,"
            " output logic [W-1:0] l); assign u = v[sel +: 4];"
            " assign d = v[sel -: 4]; assign l = v[sel*W +: W]; endmodule")
        self.assertNotIn("Unsupported", kinds(module))
        up, down, lane = (strip(p["value"]) for p in module["processes"])
        self.assertEqual(up, {
            "kind": "ArraySel", "name": "v", "indices": [],
            "part": {"mode": "up", "left": {"kind": "Ident", "name": "sel"},
                     "right": {"kind": "Int", "value": 4}}})
        self.assertEqual(down["part"]["mode"], "down")
        # `sel*W` keeps its value-tier meaning: a 32-bit product.
        self.assertEqual(lane["part"]["left"]["kind"], "Binary")
        self.assertEqual(lane["part"]["left"]["op"], "*")
        self.assertEqual(lane["part"]["right"], {"kind": "ParamRef", "name": "W"})

    def test_runtime_base_on_nonzero_range(self):
        module = self.extract(
            "module top (input logic [7:4] q, input logic [2:0] sel,"
            " output logic [1:0] y); assign y = q[sel +: 2]; endmodule")
        self.assertNotIn("Unsupported", kinds(module))
        self.assertEqual(module["processes"][0]["value"]["kind"], "ArraySel")

    def test_signed_runtime_base_is_loud(self):
        module = self.extract(
            "module top (input logic [7:0] v, input logic [2:0] sel,"
            " output logic [1:0] y); assign y = v[$signed(sel) +: 2]; endmodule")
        self.assertEqual(sv_kinds(module),
                         ["RangeSelectExpression:dynamic-signed-base"])

    def test_runtime_base_wider_than_32_bits_is_refused(self):
        # A 32-bit base is admitted (both oracles read it as an int); a wider
        # one is refused with its own kind (Icarus truncates, Yosys does not).
        module = self.extract(
            "module top (input logic [7:0] v, input logic [31:0] b32,"
            " input logic [39:0] b40, output logic [3:0] y0, output logic [3:0] y1);"
            " assign y0 = v[b32 +: 4]; assign y1 = v[b40 +: 4]; endmodule")
        self.assertEqual(sv_kinds(module), ["RangeSelectExpression:dynamic-wide-base"])
        self.assertEqual(module["processes"][0]["value"]["kind"], "ArraySel")

    def test_runtime_base_outside_the_tier_keeps_legacy_refusal(self):
        module = self.extract(
            "module top (input logic [0:7] u, input logic [1:0][3:0] m,"
            " input logic [2:0] sel, output logic [1:0] y0, output logic [1:0] y1);"
            " assign y0 = u[sel +: 2]; assign y1 = m[1][sel +: 2]; endmodule")
        self.assertEqual(sv_kinds(module),
                         ["RangeSelectExpression:dynamic-indexed",
                          "RangeSelectExpression:dynamic-indexed"])

    def test_runtime_base_target_is_refused(self):
        module = self.extract(
            "module top (input logic [2:0] sel, output logic [7:0] t);"
            " always_comb begin t = 8'h00; t[sel +: 2] = 2'b11; end endmodule")
        self.assertEqual(sv_kinds(module), ["AssignmentExpression:target"])

    def test_overhanging_procedural_targets_stay_symbolic(self):
        module = self.extract(
            "module top #(parameter int N = 4) (input logic [3:0] b,"
            " output logic [7:0] w); always_comb begin w = '0;"
            " w[N-6 +: 4] = b; end endmodule")
        self.assertNotIn("Unsupported", kinds(module))
        target = strip(module["processes"][0]["body"]["stmts"][1]["target"])
        self.assertEqual(target["kind"], "ArraySel")
        self.assertEqual(target["part"]["left"]["kind"], "Binary")


if __name__ == "__main__":
    unittest.main()
