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

    def test_dynamic_fixed_unpacked_target_expands_to_cells(self):
        module = self.extract(
            "module top (input logic [3:0] source, input logic [1:0] index,"
            " output logic [3:0] out [0:1]);"
            " always_comb out[index] = source; endmodule")
        statement = module["processes"][0]["body"]
        self.assertEqual(statement["kind"], "If")
        self.assertEqual(statement["cond"]["op"], "===")
        self.assertEqual(statement["then"]["target"]["name"], "out[0]")
        self.assertEqual(statement["else"]["then"]["target"]["name"], "out[1]")
        self.assertIsNone(statement["else"]["else"])

    def test_dynamic_fixed_unpacked_read_expands_to_conditionals(self):
        module = self.extract(
            "module top (input logic [2:0] index, input logic [7:0] a [0:3],"
            " output logic [7:0] y); always_comb y = a[index]; endmodule")
        value = module["processes"][0]["body"]["value"]
        self.assertEqual(value["kind"], "Ternary")
        self.assertEqual(value["cond"]["op"], "===")
        names = []
        while value["kind"] == "Ternary":
            names.append(value["then"]["name"])
            value = value["else"]
        self.assertEqual(names, ["a[0]", "a[1]", "a[2]", "a[3]"])
        self.assertEqual(value["kind"], "Literal")

    def test_parameter_fixed_unpacked_read_retains_array_decl(self):
        module = self.extract(
            "module top #(parameter int K = 2) (input logic [1:0] index,"
            " output logic [7:0] y); logic [7:0] a [0:K-1];"
            " always_comb y = a[index]; endmodule")
        self.assertEqual(module["decls"][0]["kind"], "UnpackedDecl")
        self.assertEqual(module["decls"][0]["unpacked"][0]["lsb"]["kind"],
                         "Binary")

    def test_nested_dynamic_fixed_unpacked_read_expands_to_conditionals(self):
        module = self.extract(
            "module top (input logic i, input logic [1:0] j,"
            " input logic [7:0] a [0:1][0:2], output logic [7:0] y);"
            " always_comb y = a[i][j]; endmodule")
        value = module["processes"][0]["body"]["value"]
        names = []
        while value["kind"] == "Ternary":
            names.append(value["then"]["name"])
            value = value["else"]
        self.assertEqual(names, ["a[0][0]", "a[0][1]", "a[0][2]",
                                 "a[1][0]", "a[1][1]", "a[1][2]"])
        self.assertEqual(value["kind"], "Literal")

    def test_nested_mixed_dynamic_fixed_unpacked_read_expands_to_one_dimension(self):
        module = self.extract(
            "module top (input logic i, input logic [1:0] j,"
            " input logic [7:0] a [0:1][0:2], output logic [7:0] y);"
            " always_comb y = a[i][1]; endmodule")
        value = module["processes"][0]["body"]["value"]
        names = []
        while value["kind"] == "Ternary":
            names.append(value["then"]["name"])
            value = value["else"]
        self.assertEqual(names, ["a[0][1]", "a[1][1]"])
        self.assertEqual(value["kind"], "Literal")

    def test_nested_dynamic_fixed_unpacked_target_expands_to_conditionals(self):
        module = self.extract(
            "module top (input logic i, input logic [1:0] j,"
            " input logic [7:0] v, output logic [7:0] a [0:1][0:2]);"
            " always_comb a[i][j] = v; endmodule")
        statement = module["processes"][0]["body"]
        names = []
        while isinstance(statement, dict) and statement["kind"] == "If":
            names.append(statement["then"]["target"]["name"])
            statement = statement["else"]
        self.assertEqual(names, ["a[0][0]", "a[0][1]", "a[0][2]",
                                 "a[1][0]", "a[1][1]", "a[1][2]"])
        self.assertIsNone(statement)

    def test_nested_mixed_dynamic_fixed_unpacked_target_constrains_constant(self):
        module = self.extract(
            "module top (input logic i, input logic [7:0] v,"
            " output logic [7:0] a [0:1][0:2]);"
            " always_comb a[i][1] = v; endmodule")
        statement = module["processes"][0]["body"]
        names = []
        while isinstance(statement, dict) and statement["kind"] == "If":
            names.append(statement["then"]["target"]["name"])
            statement = statement["else"]
        self.assertEqual(names, ["a[0][1]", "a[1][1]"])
        self.assertIsNone(statement)

    def test_parameter_fixed_unpacked_target_remains_loud(self):
        module = self.extract(
            "module top #(parameter int K = 0) (input logic [3:0] source,"
            " output logic [3:0] out [0:1]);"
            " always_comb out[K] = source; endmodule")
        statement = module["processes"][0]["body"]
        self.assertEqual(statement["kind"], "Unsupported")
        self.assertEqual(statement["sv_kind"], "ElementSelect:default-point-index")

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
