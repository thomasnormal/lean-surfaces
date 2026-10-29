"""Packed-array select paths (`ArraySel`) in sv-0.2 symbolic mode.

Nested selects, non-canonical ranges with symbolic labels and indexed part
selects with symbolic bases are emitted as ONE `ArraySel` node carrying the
raw declared labels; Lean normalizes them against the declaration's symbolic
dimensions. Every other select keeps its legacy BitSel/PartSel encoding.
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


class SymbolicArraySelects(unittest.TestCase):
    def extract(self, source):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            return json.loads(out.read_text())["design"]["modules"][0]

    def test_nested_generate_target_keeps_genvar_labels(self):
        module = self.extract(
            "module top #(parameter int N = 4) (input logic [N-1:0] a, b,"
            " output logic [N*N-1:0] y); logic [N-1:0][N-1:0] pp;"
            " genvar i, j; for (i = 0; i < N; i++) begin : gi"
            " for (j = 0; j < N; j++) begin : gj"
            " assign pp[i][j] = a[j] & b[i]; end end assign y = pp; endmodule")
        self.assertNotIn("Unsupported", kinds(module))
        cell = module["generates"][0]["body"][0]["body"][0]
        self.assertEqual(strip(cell["target"]), {
            "kind": "ArraySel", "name": "pp",
            "indices": [{"kind": "GenvarRef", "name": "i"},
                        {"kind": "GenvarRef", "name": "j"}],
            "part": None})
        # 1-D canonical reads keep the legacy node.
        self.assertEqual(cell["value"]["left"]["kind"], "BitSel")

    def test_row_part_select_is_symbolic(self):
        module = self.extract(
            "module top #(parameter int N = 4) (output logic [N-1:0] y);"
            " logic [N-1:0][N:0] s; assign s = '0;"
            " assign y = s[N-1][N:1]; endmodule")
        value = strip(module["processes"][1]["value"])
        self.assertEqual(value["kind"], "ArraySel")
        self.assertEqual(value["indices"], [{
            "kind": "Binary", "op": "-", "left": {"kind": "ParamRef", "name": "N"},
            "right": {"kind": "Int", "value": 1}}])
        self.assertEqual(value["part"], {
            "mode": "range", "left": {"kind": "ParamRef", "name": "N"},
            "right": {"kind": "Int", "value": 1}})

    def test_canonical_single_selects_stay_legacy(self):
        module = self.extract(
            "module top (input logic [7:0] a, output logic [3:0] y, output logic z);"
            " logic [1:0][3:0] m; assign m = a; assign y = m[1];"
            " assign z = a[3]; endmodule")
        self.assertEqual([p["value"]["kind"] for p in module["processes"][1:]],
                         ["BitSel", "BitSel"])

    def test_noncanonical_genvar_index_uses_labels(self):
        module = self.extract(
            "module top #(parameter int N = 4) (input logic [N:1] a,"
            " output logic [N:1] y); genvar i;"
            " for (i = 1; i <= N; i++) begin : g assign y[i] = a[i]; end endmodule")
        self.assertNotIn("Unsupported", kinds(module))
        cell = module["generates"][0]["body"][0]
        self.assertEqual(strip(cell["target"]), {
            "kind": "ArraySel", "name": "y",
            "indices": [{"kind": "GenvarRef", "name": "i"}], "part": None})

    def test_literal_noncanonical_select_keeps_legacy_fold(self):
        module = self.extract(
            "module top (input logic [10:3] a, output logic y);"
            " assign y = a[10]; endmodule")
        value = module["processes"][0]["value"]
        self.assertEqual(value["kind"], "BitSel")
        self.assertEqual(value["index"]["value"], 7)

    def test_indexed_part_with_symbolic_base(self):
        module = self.extract(
            "module top (input logic [23:0] a, output logic [23:0] y);"
            " logic [5:0][3:0] m; genvar i;"
            " for (i = 0; i < 6; i++) begin : g assign m[i] = a[i*4 +: 4]; end"
            " assign y = m; endmodule")
        value = strip(module["generates"][0]["body"][0]["value"])
        self.assertEqual(value["kind"], "ArraySel")
        self.assertEqual(value["indices"], [])
        self.assertEqual(value["part"]["mode"], "up")
        self.assertEqual(value["part"]["right"], {"kind": "Int", "value": 4})

    def test_dynamic_nested_index_on_3d_is_loud(self):
        module = self.extract(
            "module top (input logic [1:0] k, output logic [3:0] y);"
            " logic [1:0][2:0][3:0] m; assign m = '0;"
            " assign y = m[1][k]; endmodule")
        value = module["processes"][1]["value"]
        self.assertEqual(value["kind"], "Unsupported")
        self.assertEqual(value["sv_kind"], "ElementSelectExpression:nested-dynamic")

    def test_dynamic_nested_index_on_2d_keeps_legacy(self):
        module = self.extract(
            "module top (input logic k, output logic y);"
            " logic [1:0][3:0] m; assign m = '0;"
            " assign y = m[k][2]; endmodule")
        value = module["processes"][1]["value"]
        self.assertEqual(value["kind"], "BitSel")
        self.assertEqual(value["value"]["kind"], "BitSel")

    def test_unexpected_failure_on_3d_chain_is_loud(self):
        # A failure inside the ArraySel builder must not fall back to the
        # legacy nested encoding (exact for two dimensions only).
        original = extract._sym_tree_static

        def boom(node):
            raise RuntimeError("injected")

        extract._sym_tree_static = boom
        try:
            module = self.extract(
                "module top (output logic [3:0] y, output logic z);"
                " logic [1:0][2:0][3:0] m; logic [1:0][3:0] n;"
                " assign m = '0; assign n = '0;"
                " assign y = m[1][2]; assign z = n[1][2]; endmodule")
        finally:
            extract._sym_tree_static = original
        value = module["processes"][2]["value"]
        self.assertEqual(value["kind"], "Unsupported")
        self.assertEqual(value["sv_kind"], "ElementSelectExpression:array-select")
        # A 2-D root keeps the legacy fallback (exact there).
        self.assertEqual(module["processes"][3]["value"]["kind"], "BitSel")
        self.assertEqual(module["processes"][3]["value"]["value"]["kind"], "BitSel")


if __name__ == "__main__":
    unittest.main()
