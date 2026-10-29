"""Default-point folds and selects in sv-0.2 symbolic mode (2026-10-28, WP1).

slang elaborates a module ONCE, at its default parameters (a library module
at ITS defaults, a generate body at its first iteration). Whatever the
extractor reads off that elaboration is a fact about the default point, and
three such facts used to reach the Lean family silently:

* An unsized INT-class constant (`-1`, `37`, `N - 1`, `-7 / 2`) assigned to a
  parameter- or genvar-width target was folded to a literal of the DEFAULT
  width, which Lean zero-extended at every other point. It is now emitted
  UNCONVERTED (Lean fits it at the instantiated width); a sized signed
  literal is a `SignedResize` of the literal at its own width; any other
  signed constant is loud in a parametric family
  (`ConversionExpression:signed-constant`).
* A STATIC select label (literals and parameters) over a parameter-dependent
  range took the legacy offset encoding whenever the range was `[m:0]` at the
  default point; it is now an `ArraySel` path, normalized per point.
* A NET (`wire logic`, scalar `wire`, an output net port) passed the load gate
  although its undriven bits read z; it is refused (`NetSymbol:net-z`,
  `PortSymbol:net-z`). Input net ports stay admitted.

And a fourth, a refusal kind: a `$bits(signal)` label is an elaboration-time
constant (an `ArraySel` label), and a `$high`/`$size` one is refused as such
(`…:query-label`) instead of as a run-time base (`…:dynamic-signed-base`).

Repair round (verifier round 2): `$bits` is static only of a declared signal
whose declaration carries its width per point; a packed struct/union or a
fixed unpacked array whose SHAPE depends on the point is refused at its
declaration (`…:default-point-aggregate`, `VariableSymbol:default-point-
array`); a signed operand that reads a signal keeps `ConversionExpression:
width`.
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


def strip(node):
    if isinstance(node, dict):
        return {k: strip(v) for k, v in node.items()
                if k not in ("span", "resolved_width", "width")}
    if isinstance(node, list):
        return [strip(v) for v in node]
    return node


def kinds(node):
    return [n["sv_kind"] for n in find(node, lambda n: n.get("kind") == "Unsupported")]


class SymbolicDefaultPoint(unittest.TestCase):
    def extract_all(self, source, top="top"):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / "fixture.sv"
            out = Path(directory) / "fixture.sv.json"
            src.write_text(source)
            extract.process_symbolic(top, [str(src)], [], str(out))
            return json.loads(out.read_text())["design"]["modules"]

    def extract(self, source):
        return self.extract_all(source)[0]

    def values(self, module):
        return {p["target"]["name"]: strip(p["value"]) for p in module["processes"]
                if p.get("kind") == "Assign" and p["target"].get("kind") == "Ident"}

    # --- (a) INT-class constants -------------------------------------------

    def test_int_class_constants_stay_unconverted(self):
        module = self.extract(
            "module top #(parameter int N = 7) (output logic [N+1:0] o1, o2, o3,"
            " o4, o5); assign o1 = -1; assign o2 = 37; assign o3 = N - 1;"
            " assign o4 = -7 / 2; assign o5 = ~0; endmodule")
        values = self.values(module)
        self.assertEqual(values["o1"], {"kind": "Unary", "op": "-",
                                        "operand": {"kind": "Int", "value": 1}})
        self.assertEqual(values["o2"], {"kind": "Int", "value": 37})
        self.assertEqual(values["o3"]["kind"], "Binary")
        self.assertEqual(values["o3"]["left"], {"kind": "ParamRef", "name": "N"})
        self.assertEqual(values["o4"]["op"], "s/")
        self.assertEqual(values["o5"]["op"], "~")
        self.assertFalse(find(module, lambda n: n.get("kind") == "Literal"))
        self.assertEqual(kinds(module), [])

    def test_genvar_width_target_keeps_the_constant(self):
        module = self.extract(
            "module top (output logic [5:0] neg);"
            " for (genvar g = 1; g <= 3; g++) begin : gl"
            " assign neg[(g*(g-1))/2 +: g] = -1; end endmodule")
        loop, = module["generates"]
        assign, = loop["body"]
        self.assertEqual(strip(assign["value"]),
                         {"kind": "Unary", "op": "-", "operand": {"kind": "Int", "value": 1}})

    def test_child_constants_stay_unconverted(self):
        modules = self.extract_all(
            "module cs #(parameter int W = 2) (output logic [W-1:0] ones, big);"
            " assign ones = -1; assign big = 37; endmodule"
            " module top (output logic [7:0] o, b);"
            " cs #(.W(8)) u (.ones(o), .big(b)); endmodule")
        child = [m for m in modules if m["name"] == "cs"][0]
        values = self.values(child)
        self.assertEqual(values["ones"]["kind"], "Unary")
        self.assertEqual(values["big"], {"kind": "Int", "value": 37})

    def test_signed_parameter_operand_is_sign_preserving(self):
        # `B * 2` with a `byte` B: the propagated conversion of B into the
        # signed 32-bit operation keeps B unconverted (sign extension).
        module = self.extract(
            "module top #(parameter int N = 7, parameter byte B = -3)"
            " (output logic [N+1:0] o1, o2); assign o1 = B * 2; assign o2 = B;"
            " endmodule")
        values = self.values(module)
        self.assertEqual(values["o1"]["left"], {"kind": "ParamRef", "name": "B"})
        self.assertEqual(values["o2"], {"kind": "ParamRef", "name": "B"})

    def test_zero_extension_of_a_signed_parameter_is_a_resize(self):
        # A PROPAGATED conversion into an UNSIGNED type zero-extends a negative
        # operand: never emitted as a (sign-extended) INT tree. It was loud
        # (`ConversionExpression:width`) until the round 3 folds, which keep
        # it as `Resize` of the parameter (`_sym_unsigned_simple_operand`):
        # Lean zero-extends the parameter's own 32-bit value (§11.8.2).
        module = self.extract(
            "module top #(parameter int N = 7) (input logic [39:0] a,"
            " output logic [39:0] o); assign o = a + N; endmodule")
        self.assertEqual(kinds(module), [])
        self.assertEqual(self.values(module)["o"]["right"],
                         {"kind": "Resize", "operand": {"kind": "ParamRef", "name": "N"}})

    def test_sized_signed_literal_is_a_signed_resize(self):
        module = self.extract(
            "module top #(parameter int N = 7) (output logic [N+1:0] o1, o2);"
            " assign o1 = 4'sb1000; assign o2 = 12'shF80; endmodule")
        values = self.values(module)
        for name, width in (("o1", 4), ("o2", 12)):
            node = [p["value"] for p in module["processes"] if p["target"]["name"] == name][0]
            self.assertEqual(node["kind"], "SignedResize")
            self.assertEqual(node["operand"]["kind"], "Literal")
            self.assertEqual(node["operand"]["width"], width)
        self.assertEqual(kinds(module), [])
        self.assertTrue(values)

    def test_other_signed_constants_are_loud_in_a_family(self):
        module = self.extract(
            "module top #(parameter int N = 7) (output logic [N+1:0] o);"
            " assign o = (3 > 2) ? -1 : 2; endmodule")
        self.assertEqual(kinds(module), ["ConversionExpression:signed-constant"])

    def test_other_signed_constants_fold_without_parameters(self):
        module = self.extract(
            "module top (output logic [8:0] o); assign o = (3 > 2) ? -1 : 2; endmodule")
        self.assertEqual(kinds(module), [])
        self.assertEqual(strip(module["processes"][0]["value"]),
                         {"kind": "Literal", "bits": "111111111"})

    # --- (b) static labels over parameter-dependent ranges ------------------

    def test_static_labels_take_the_array_path(self):
        module = self.extract(
            "module top #(parameter int N = 4, parameter int P = 1)"
            " (input logic [N-1:0] v, output logic o1, o3, output logic [1:0] o2);"
            " assign o1 = v[1]; assign o2 = v[1 +: 2]; assign o3 = v[P]; endmodule")
        values = self.values(module)
        self.assertEqual(values["o1"], {"kind": "ArraySel", "name": "v",
                                        "indices": [{"kind": "Int", "value": 1}],
                                        "part": None})
        self.assertEqual(values["o2"]["part"]["mode"], "up")
        self.assertEqual(values["o3"]["indices"], [{"kind": "ParamRef", "name": "P"}])

    def test_localparam_range_static_label_target(self):
        module = self.extract(
            "module top #(parameter int N = 8) (input logic b, output logic [1:0] o);"
            " localparam int K = N - 4; logic [K-1:0] t;"
            " always_comb begin t = '0; t[1 +: 1] = b; end"
            " assign o = t[1 +: 2]; endmodule")
        targets = find(module, lambda n: n.get("kind") == "ArraySel" and n.get("name") == "t")
        self.assertEqual(len(targets), 2)
        self.assertFalse(find(module, lambda n: n.get("kind") in ("BitSel", "PartSel")))

    def test_literal_bounds_and_genvar_labels_keep_the_legacy_path(self):
        module = self.extract(
            "module top #(parameter int N = 4) (input logic [7:0] w,"
            " input logic [N-1:0] v, output logic o, output logic [N-1:0] y);"
            " assign o = w[1];"
            " for (genvar i = 0; i < N; i++) begin : g assign y[i] = v[i]; end"
            " endmodule")
        self.assertEqual(module["processes"][0]["value"]["kind"], "BitSel")
        loop, = module["generates"]
        assign, = loop["body"]
        self.assertEqual(assign["target"]["kind"], "BitSel")
        self.assertEqual(assign["value"]["kind"], "BitSel")

    # --- (c) nets ------------------------------------------------------------

    def test_nets_are_refused(self):
        module = self.extract(
            "module top (input logic a, input wire b, output wire yo,"
            " output wire logic [1:0] yl, output y1, output logic t);"
            " wire w; wire logic [1:0] wl; assign t = a; endmodule")
        names = {p["name"]: p for p in module["ports"] if p.get("kind") == "Port"}
        self.assertEqual(sorted(names), ["a", "b", "t"])
        self.assertEqual(sorted(kinds(module["ports"])), ["PortSymbol:net-z"] * 3)
        self.assertEqual(sorted(kinds(module["decls"]) + kinds(module["others"])),
                         ["NetSymbol:net-z", "NetSymbol:net-z"])

    def test_implicit_ranged_net_keeps_its_unrecoverable_type(self):
        module = self.extract(
            "module top (input logic [3:0] b, output wire [7:0] w);"
            " assign w[3:0] = b; endmodule")
        port = [p for p in module["ports"] if p.get("name") == "w"][0]
        self.assertIsNone(port["width"]["packed"])

    # --- (d) array query labels ----------------------------------------------

    def test_bits_label_is_static(self):
        module = self.extract(
            "module top #(parameter int N = 6) (input logic [N-1:0] a,"
            " input logic [7:0] v, output logic [1:0] o1, o2, output logic [7:0] y);"
            " assign o1 = v[$bits(a) - 1 -: 2]; assign o2 = v[$clog2($bits(a)) +: 2];"
            " always_comb begin y = '0; y[$bits(a) - 3 +: 2] = 2'b11; end endmodule")
        self.assertEqual(kinds(module), [])
        self.assertEqual(len(find(module, lambda n: n.get("kind") == "ArraySel")), 3)

    def test_high_label_is_a_query_refusal(self):
        module = self.extract(
            "module top #(parameter int N = 6) (input logic [N:1] a,"
            " input logic [7:0] v, output logic [1:0] o, output logic [1:0] r);"
            " assign o = v[$high(a) -: 2]; assign r = v[$clog2(a) +: 2]; endmodule")
        self.assertEqual(kinds(module), ["RangeSelectExpression:query-label",
                                         "RangeSelectExpression:dynamic-signed-base"])

    # --- repair round: default-point SHAPES and narrowed `$bits` --------------

    def test_parameter_dependent_aggregate_is_refused(self):
        module = self.extract(
            "module top #(parameter int N = 3) (input logic [N-1:0] a,"
            " input logic [1:0] b, output logic [N+1:0] o, output logic [N-1:0] x);"
            " typedef struct packed { logic [N-1:0] x; logic [1:0] y; } st_t;"
            " st_t s; assign s = {a, b}; assign o = s; assign x = s.x; endmodule")
        self.assertEqual(kinds(module), ["VariableSymbol:default-point-aggregate"])

    def test_aggregate_dependence_through_localparam_typedef_and_enum(self):
        module = self.extract(
            "module top #(parameter int N = 3) (input logic [7:0] v, output logic [7:0] o);"
            " localparam int K = N - 1; localparam int L = 5;"
            " typedef logic [N-1:0] w_t; typedef logic [L-1:0] f_t;"
            " typedef enum logic [N-1:0] {A, B} e_t;"
            " typedef struct packed { logic [K:0] x; } s1_t;"
            " typedef struct packed { w_t x; } s2_t;"
            " typedef struct packed { e_t x; } s3_t;"
            " typedef union packed { f_t x; logic [4:0] y; } u_t;"
            " typedef struct packed { logic [$bits(v)-1:0] x; } s4_t;"
            " s1_t s1; s2_t s2; s3_t s3; u_t u; s4_t s4; assign o = v; endmodule")
        refused = sorted(n["text"].split()[-1] for n in find(
            module["decls"], lambda n: n.get("kind") == "Unsupported"))
        self.assertEqual(refused, ["s1", "s2", "s3"])
        self.assertEqual(sorted(d["name"] for d in module["decls"] if d.get("kind") == "Var"),
                         ["s4", "u"])

    def test_package_aggregate_and_one_point_module_keep_their_encoding(self):
        modules = self.extract_all(
            "package pk; parameter int PW = 4;"
            " typedef struct packed { logic [PW-1:0] a; logic b; } p_t; endpackage"
            " module top #(parameter int N = 3) (input logic [4:0] a, output logic [4:0] o);"
            " import pk::*; p_t s; assign s = a; assign o = s; endmodule")
        self.assertEqual(kinds(modules), [])
        module = self.extract(
            "module top (input logic [4:0] a, output logic [4:0] o);"
            " localparam int N = 3;"
            " typedef struct packed { logic [N-1:0] x; logic [1:0] y; } st_t;"
            " st_t s; assign s = a; assign o = s; endmodule")
        self.assertEqual(kinds(module), [])

    def test_parameter_dependent_aggregate_parameter_type_is_unrecoverable(self):
        module = self.extract(
            "module top #(parameter int N = 3) (output logic [N+1:0] o);"
            " typedef struct packed { logic [N-1:0] x; logic [1:0] y; } st_t;"
            " localparam st_t P = 37; assign o = P; endmodule")
        param, = [p for p in module["params"] if p["name"] == "P"]
        self.assertIsNone(param["type"]["packed"])

    def test_parameter_dependent_unpacked_array_is_refused(self):
        module = self.extract(
            "module top #(parameter int N = 3, parameter int K = 2)"
            " (input logic [N-1:0] d, output logic [N-1:0] q);"
            " localparam int L = 2; typedef logic [N-1:0] w_t;"
            " logic [N-1:0] m1 [0:K-1]; w_t m2 [0:1]; logic [N-1:0] m3 [0:L-1];"
            " assign m3[0] = d; assign q = m3[0]; endmodule")
        self.assertEqual(kinds(module), ["VariableSymbol:default-point-array"] * 2)
        self.assertEqual(sorted(d["name"] for d in module["decls"] if d.get("kind") == "Var"),
                         ["m3[0]", "m3[1]"])

    def test_bits_of_a_dependent_aggregate_or_an_expression_is_a_query_refusal(self):
        module = self.extract(
            "module top #(parameter int N = 3) (input logic [N-1:0] a,"
            " input logic [31:0] v, output logic [1:0] o1, o2, o3);"
            " typedef struct packed { logic [N-1:0] x; logic [1:0] y; } st_t; st_t s;"
            " assign s = {a, 2'b00};"
            " assign o1 = v[$bits(s) +: 2]; assign o2 = v[$bits(a[1:0]) +: 2];"
            " assign o3 = v[$bits(a + 1'b1) +: 2]; endmodule")
        self.assertEqual(sorted(kinds(module)),
                         ["RangeSelectExpression:query-label"] * 3
                         + ["VariableSymbol:default-point-aggregate"])

    def test_bits_of_a_fixed_aggregate_is_static(self):
        module = self.extract(
            "module top #(parameter int N = 4) (input logic [31:0] v, input logic [2:0] c,"
            " output logic [1:0] o1, output logic [2:0] x);"
            " typedef struct packed { logic [2:0] x; logic [2:0] y; } st_t; st_t s;"
            " assign s = {c, ~c}; assign o1 = v[$bits(s) +: 2]; assign x = s.x; endmodule")
        self.assertEqual(kinds(module), [])
        self.assertTrue(find(module, lambda n: n.get("kind") == "SysCall"
                             and n.get("name") == "$bits"))

    def test_signed_operand_reading_a_signal_keeps_the_width_refusal(self):
        module = self.extract(
            "module top #(parameter int N = 7) (input logic [3:0] a, output logic [N:0] o);"
            " assign o = $signed(a) * -2; endmodule")
        self.assertEqual(kinds(module), ["ConversionExpression:width"])


if __name__ == "__main__":
    unittest.main()
