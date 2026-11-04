"""Parameter typing and context widths in sv-0.2 symbolic mode (2026-10-28,
F2 repair round 2).

* A parameter with a RANGE but no type (`parameter [3:0] V`,
  `parameter signed [3:0] V`) is typed: IEEE 1800-2023 6.20.2 fixes its range
  (unsigned without `signed`) whatever the override, so the envelope carries
  its `PackedType` (symbolic dimensions) and `signed` where it departs from
  the default. A dimensioned keyword type (`logic signed [3:0]`, `bit [4:0]`)
  gets the same symbolic dimensions instead of `packed: null`.
* A RANGELESS implicit type with a signing keyword (`parameter signed P`)
  stays untyped (`type: null`: its range is the final value's) and records
  the keyword as `signed`.
* A signed operand sign-extended in a constant position (`SB + 5` with a
  `byte` SB) is a `SignedResize`; a constant select label that fails to
  convert keeps its own refusal kind instead of a run-time-base one.
* A sized unsigned literal widened by its VALUE context (`a + 1'b1`) is a
  `Resize` of the literal, not a literal folded at the default width.
* Implicitly typed NETS and net ports (`output wire [7:0]`) keep
  `packed: null` (a partially driven net's undriven bits are z, which the
  semantic tier does not model).
"""
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


def dims(ptype):
    return [(d["msb"].get("value"), d["lsb"].get("value")) for d in ptype["packed"]]


class SymbolicParamWidths(unittest.TestCase):
    def extract(self, source):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic("top", [str(src)], [], str(out))
            return json.loads(out.read_text())["design"]["modules"][0]

    def test_ranged_and_dimensioned_parameter_types(self):
        module = self.extract(
            "module top #(parameter P = 3'd5, parameter [3:0] V = 4'd9,"
            " parameter signed [3:0] SV = -4'sd2, parameter [31:0] U = 5,"
            " parameter logic signed [3:0] S = -4'sd2, parameter bit [4:0] B = 5'd30,"
            " parameter signed SX = 4'd3, parameter unsigned UX = 7)"
            " (input logic [15:0] v, output logic [1:0] o);"
            " assign o = v[V + 4'd8 +: 2]; endmodule")
        params = {p["name"]: p for p in module["params"]}
        self.assertIsNone(params["P"]["type"])
        self.assertNotIn("signed", params["P"])
        self.assertEqual(dims(params["V"]["type"]), [(3, 0)])
        self.assertNotIn("signed", params["V"])
        self.assertEqual(dims(params["SV"]["type"]), [(3, 0)])
        self.assertIs(params["SV"]["signed"], True)
        self.assertEqual(dims(params["U"]["type"]), [(31, 0)])
        self.assertIs(params["U"]["signed"], False)
        self.assertEqual(dims(params["S"]["type"]), [(3, 0)])
        self.assertIs(params["S"]["signed"], True)
        self.assertEqual(dims(params["B"]["type"]), [(4, 0)])
        self.assertIsNone(params["SX"]["type"])
        self.assertIs(params["SX"]["signed"], True)
        self.assertIsNone(params["UX"]["type"])
        self.assertIs(params["UX"]["signed"], False)

    def test_parametric_parameter_range_stays_symbolic(self):
        module = self.extract(
            "module top #(parameter int W = 4, parameter [W-1:0] K = 3)"
            " (input logic [15:0] v, output logic o); assign o = v[K]; endmodule")
        k = [p for p in module["params"] if p["name"] == "K"][0]
        self.assertEqual(k["type"]["packed"][0]["msb"]["kind"], "Binary")

    def test_scalar_package_parameters_stay_qualified(self):
        module = self.extract(
            "package pk; parameter int W = 4; endpackage "
            "module top #(parameter int N = 2) ("
            "input logic [pk::W+N-1:0] a, output logic [pk::W-1:0] o); "
            "always_comb o = a[pk::W-1:0]; endmodule")
        package_params = module["package_params"]
        self.assertEqual([(p["package"], p["name"], p["resolved"])
                          for p in package_params], [("pk", "W", 4)])
        self.assertEqual(
            module["ports"][0]["width"]["packed"][0]["msb"]["left"]["left"]["from_package"],
            "pk")
        self.assertFalse(find(module, lambda n: n.get("kind") == "Unsupported"))

    def test_untyped_scalar_package_parameters_stay_qualified(self):
        module = self.extract(
            "package pk; parameter W = 4; localparam L = W + 1; endpackage "
            "module top (input logic [3:0] a, output logic [3:0] o); "
            "always_comb o = a ^ pk::W ^ pk::L; endmodule")
        self.assertEqual(
            [(p["package"], p["name"], p["type"], p["resolved"])
             for p in module["package_params"]],
            [("pk", "W", None, 4), ("pk", "L", None, 5)])
        refs = find(module, lambda n: n.get("kind") == "ParamRef")
        self.assertEqual(
            [(r["name"], r.get("from_package")) for r in refs],
            [("W", "pk"), ("W", "pk"), ("L", "pk")])
        self.assertFalse(find(module, lambda n: n.get("kind") == "Unsupported"))

    def test_fixed_packed_package_parameters_stay_qualified(self):
        module = self.extract(
            "package pk; parameter logic [3:0] P = 4'b1010; endpackage "
            "module top (input logic [3:0] a, output logic [3:0] o); "
            "always_comb o = a ^ pk::P; endmodule")
        package_params = module["package_params"]
        self.assertEqual([(p["package"], p["name"], p["resolved"])
                          for p in package_params], [("pk", "P", 10)])
        self.assertEqual(package_params[0]["type"]["packed"][0]["msb"]["value"], 3)
        refs = find(module, lambda n: n.get("kind") == "ParamRef")
        self.assertEqual(len(refs), 1)
        self.assertEqual((refs[0]["name"], refs[0]["from_package"]), ("P", "pk"))
        self.assertFalse(find(module, lambda n: n.get("kind") == "Unsupported"))

    def test_signed_flat_variable_is_retained(self):
        module = self.extract(
            "module top (input logic signed [3:0] a, input logic signed [3:0] b,"
            " output logic signed [3:0] y, output logic signed lt);"
            " logic signed [3:0] t; always_comb begin t = a; y = t; lt = t < b; end"
            " endmodule")
        decl = next(d for d in module["decls"] if d.get("name") == "t")
        self.assertIs(decl.get("signed"), True)
        self.assertFalse(find(module, lambda n: n.get("kind") == "Unsupported"))

    def test_signed_single_driver_net_is_retained(self):
        module = self.extract(
            "module top (input logic signed [3:0] a, input logic signed [3:0] b,"
            " output logic signed [3:0] y, output logic signed lt);"
            " wire signed [3:0] w; assign w = a;"
            " always_comb begin y = w; lt = w < b; end endmodule")
        decl = next(d for d in module["decls"] if d.get("name") == "w")
        self.assertEqual(decl.get("kind"), "Var")
        self.assertIs(decl.get("signed"), True)
        self.assertIs(decl.get("net_as_variable"), True)
        self.assertFalse(find(module, lambda n: n.get("kind") == "Unsupported"))

    def test_signed_unresolved_net_stays_loud(self):
        module = self.extract(
            "module top (input logic signed [3:0] a, output logic signed [3:0] y);"
            " wire signed [3:0] w; always_comb y = w; endmodule")
        decl = next(d for d in module["decls"] if d.get("kind") == "Unsupported")
        self.assertEqual(decl.get("sv_kind"), "NetSymbol:signed")

    def test_fixed_root_signed_packed_struct_is_retained(self):
        module = self.extract(
            "module top(input logic [7:0] a, output logic signed [7:0] y,"
            " output logic lt);"
            " typedef struct packed signed { logic [7:0] x; } st_t;"
            " st_t s; always_comb begin s = a; y = s; lt = s < 8'sd0; end"
            " endmodule")
        decl = next(d for d in module["decls"] if d.get("name") == "s")
        self.assertIs(decl.get("signed"), True)
        self.assertFalse(find(module, lambda n: n.get("kind") == "Unsupported"))

    def test_parametric_packed_package_width_stays_loud(self):
        module = self.extract(
            "package pk; parameter int W = 4; "
            "parameter logic [W-1:0] P = '0; endpackage "
            "module top (input logic [3:0] a, output logic [3:0] o); "
            "always_comb o = a ^ pk::P; endmodule")
        self.assertEqual([p["name"] for p in module["package_params"]], ["W"])

    def test_signed_widening_in_constant_label(self):
        module = self.extract(
            "module top #(parameter byte SB = -8'sd3, parameter logic signed [3:0] S = -4'sd2)"
            " (input logic [15:0] v, output logic [3:0] o, output logic [3:0] p);"
            " assign o = v[SB + 5 +: 4]; assign p = v[S * -1 +: 4]; endmodule")
        self.assertEqual(find(module, lambda n: n.get("kind") == "Unsupported"), [])
        resized = find(module, lambda n: n.get("kind") == "SignedResize")
        self.assertEqual(sorted(n["width"] for n in resized), [32, 32])

    def test_constant_label_unsigned_widening_is_a_resize(self):
        # A signed parameter widened into an UNSIGNED label (zero extension,
        # IEEE 1800-2023 11.8.2) was loud with the conversion's own kind; since
        # the round 3 repair the symbolic positions of a parametric family
        # keep it as the `Resize` marker the constant tier zero-extends
        # exactly (`_sym_unsigned_simple_operand`) — never a run-time kind.
        module = self.extract(
            "module top #(parameter byte SB = 8'sd3) (input logic [15:0] v,"
            " output logic [3:0] o); assign o = v[SB + 32'd1 +: 4]; endmodule")
        kinds = [n["sv_kind"] for n in find(module, lambda n: n.get("kind") == "Unsupported")]
        self.assertFalse(any("dynamic" in k for k in kinds), kinds)
        markers = find(module, lambda n: n.get("kind") == "Resize"
                       and n["operand"].get("kind") == "ParamRef"
                       and n["operand"].get("name") == "SB")
        self.assertEqual([n["width"] for n in markers], [32])

    def test_widened_sized_literal_is_a_resize(self):
        module = self.extract(
            "module top #(parameter int N = 4) (input logic [N-1:0] a,"
            " output logic [3:0] o, output logic [5:0] c);"
            " assign o = a + 1'b1; assign c = {a + 1'b1, 1'b0}; endmodule")
        resized = find(module, lambda n: n.get("kind") == "Resize"
                       and n["operand"].get("kind") == "Literal")
        self.assertEqual([(n["width"], n["operand"]["width"]) for n in resized], [(4, 1), (4, 1)])

    def test_implicit_net_port_is_loud(self):
        # WP-PROC N1: the dimensions are recovered, the partially driven net stays refused (`net-z`)
        module = self.extract(
            "module top (input logic [3:0] b, output wire [7:0] w);"
            " assign w[3:0] = b; endmodule")
        ports = [p for p in module["ports"] if p.get("kind") == "Unsupported"]
        self.assertEqual([p["sv_kind"] for p in ports], ["PortSymbol:net-z"])


if __name__ == "__main__":
    unittest.main()
