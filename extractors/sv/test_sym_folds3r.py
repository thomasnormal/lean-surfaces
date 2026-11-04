"""Round 3 repair: default-point folds in SYMBOLIC positions (sv-0.2
symbolic mode, 2026-10-28).

The value-position conversions of round 3 (`_sym_unsigned_simple_operand`,
`_sym_literal_widening`, `_sym_signed_literal_conversion`) now also apply
in the symbolic positions (`_SymPos`: case items, select labels, generate
conditions, localparam/parameter initializers, overrides) of a parametric
family:

(1) A signed parameter or genvar propagated into an unsigned context keeps
the conversion as `Resize(width, ParamRef)` — `case (a) P:` and `v[a - P]`
used to read a bare `P` that Lean sign-extended where the comparison or the
index is wider than 32 bits (verifier repros `vp_case`, `vp_idx`).

(2) A sized literal widened by its context is `Resize(width, Literal)`
(`SignedResize` for a signed literal in a signed context), not slang's
literal folded at the DEFAULT point's context width — which inflated the
width Lean computes wherever the context is narrower (`v[s + 1'b1]`).

(3) A signed constant tree without references under an assignment-like
width change (`localparam logic [N-1:0] L = -1`) keeps the tree under a
resize of the target width instead of a literal folded at the default
point's target; any other such conversion is loud
(`ConversionExpression:signed-constant`).

(4) A TYPED instance-parameter override that is a context-propagating
expression (`.P(U + 8'd100)` into `logic [15:0] P`) is loud
(`InstanceSymbol:override-context`): Icarus evaluates it at the parameter's
width (IEEE 1800-2023 10.8), Yosys 0.53 and Verilator 5.042 at its own.

A module with one point keeps the old encodings.
"""
import json
import tempfile
import unittest
from pathlib import Path

import extract


def extract_sym(source, top):
    with tempfile.TemporaryDirectory() as directory:
        src = Path(directory) / "fixture.sv"
        src.write_text(source)
        out = Path(directory) / "fixture.sv.json"
        extract.process_symbolic(top, [str(src)], [], str(out))
        return json.loads(out.read_text())


def strip(node):
    if isinstance(node, dict):
        return {k: strip(v) for k, v in node.items()
                if k not in ("span", "width", "resolved_width", "signed")}
    if isinstance(node, list):
        return [strip(v) for v in node]
    return node


def module(env):
    return env["design"]["modules"][0]


def localparams(env):
    return {p["name"]: p for p in module(env)["params"] if p["kind"] == "LocalParam"}


def assign_values(env):
    return {p["target"]["name"]: p["value"]
            for p in module(env)["processes"] if p.get("kind") == "Assign"}


def case_patterns(env):
    pats = []
    for p in module(env)["processes"]:
        if p.get("kind") != "AlwaysComb":
            continue
        for s in p["body"]["stmts"]:
            if s.get("kind") == "Case":
                pats.append([strip(q) for it in s["items"] for q in it["patterns"]])
    return pats


PARAM_MARKER = {"kind": "Resize", "operand": {"kind": "ParamRef", "name": "P"}}


class SymbolicPositionMarkers(unittest.TestCase):
    SRC = ("module top #(parameter int N = 7, parameter int P = -3) "
           "(input logic [N+1:0] a, input logic [7:0] v, output logic [1:0] o, "
           "output logic o3); "
           "always_comb begin case (a) P: o = 2'd1; default: o = 2'd0; endcase end "
           "assign o3 = v[a - P]; endmodule\n")

    def test_case_item_parameter_is_wrapped(self):
        self.assertEqual(case_patterns(extract_sym(self.SRC, "top")), [[PARAM_MARKER]])

    def test_index_parameter_is_wrapped(self):
        index = strip(assign_values(extract_sym(self.SRC, "top"))["o3"]["index"])
        self.assertEqual(index["right"], PARAM_MARKER)

    def test_wide_default_point_case_item_is_the_widening_marker(self):
        # At a default point where the case compares wider than 32 bits the
        # same conversion widens `P`: the twin, no longer
        # `ConversionExpression:width`.
        src = self.SRC.replace("N = 7", "N = 40")
        self.assertEqual(case_patterns(extract_sym(src, "top")), [[PARAM_MARKER]])

    def test_single_point_module_is_unchanged(self):
        src = ("module top (input logic [8:0] a, output logic [1:0] o); "
               "localparam int P = -3; "
               "always_comb begin case (a) P: o = 2'd1; default: o = 2'd0; endcase end "
               "endmodule\n")
        self.assertEqual(case_patterns(extract_sym(src, "top")),
                         [[{"kind": "ParamRef", "name": "P"}]])


class SymbolicPositionLiterals(unittest.TestCase):
    def test_index_literal_is_a_resize(self):
        src = ("module top #(parameter int N = 4) (input logic [N-1:0] s, "
               "input logic [15:0] v, output logic o); assign o = v[s + 1'b1]; endmodule\n")
        index = strip(assign_values(extract_sym(src, "top"))["o"]["index"])
        self.assertEqual(index["right"]["kind"], "Resize")
        self.assertEqual(index["right"]["operand"]["kind"], "Literal")

    def test_localparam_operand_literals_are_resizes(self):
        src = ("module top #(parameter int N = 16) (input logic [N-1:0] a, "
               "output logic [N-1:0] o); "
               "localparam logic [N-1:0] L = (8'd200 + 8'd100) >> 5; assign o = L ^ a; endmodule\n")
        expr = strip(localparams(extract_sym(src, "top"))["L"]["expr"])
        self.assertEqual([expr["left"]["left"]["kind"], expr["left"]["right"]["kind"]],
                         ["Resize", "Resize"])

    def test_signed_literal_initializer_is_a_signed_resize(self):
        src = ("module top #(parameter int N = 4) (input logic [N-1:0] a, "
               "output logic [N-1:0] o); "
               "localparam logic [N-1:0] S = 8'sd100; assign o = S ^ a; endmodule\n")
        expr = strip(localparams(extract_sym(src, "top"))["S"]["expr"])
        self.assertEqual(expr["kind"], "SignedResize")
        self.assertEqual(expr["operand"]["kind"], "Literal")

    def test_single_point_module_keeps_the_fold(self):
        src = ("module top (input logic [3:0] s, input logic [15:0] v, output logic o); "
               "assign o = v[s + 1'b1]; endmodule\n")
        index = strip(assign_values(extract_sym(src, "top"))["o"]["index"])
        self.assertEqual(index["right"]["kind"], "Literal")


class SymbolicSignedConstants(unittest.TestCase):
    def test_implicit_truncation_keeps_the_tree(self):
        src = ("module top #(parameter int N = 8) (input logic [N-1:0] a, "
               "output logic [N-1:0] o); "
               "localparam logic [N-1:0] L = -1; assign o = L ^ a; endmodule\n")
        expr = strip(localparams(extract_sym(src, "top"))["L"]["expr"])
        self.assertEqual(expr["kind"], "Resize")
        self.assertEqual(expr["operand"]["kind"], "Unary")

    def test_single_point_module_keeps_the_fold(self):
        src = ("module top (input logic [7:0] a, output logic [7:0] o); "
               "localparam logic [7:0] L = -1; assign o = L ^ a; endmodule\n")
        expr = strip(localparams(extract_sym(src, "top"))["L"]["expr"])
        self.assertEqual(expr["kind"], "Literal")


class TypedOverrides(unittest.TestCase):
    # A typed context-propagating override splits the tools (Icarus: the
    # parameter's width, IEEE 10.8; Yosys/Verilator: its own width): loud.
    SRC = ("module ch #(parameter logic [15:0] P = 0, parameter int Q = 0, "
           "parameter int R = 0) (input logic [15:0] a, output logic [15:0] o); "
           "assign o = P ^ Q ^ R ^ a; endmodule\n"
           "module top #(parameter int N = 8) (input logic [15:0] a, output logic [15:0] o); "
           "localparam logic [N-1:0] U = 8'd200; "
           "ch #(.P(%s), .Q(%s), .R(N + 2)) c (.a(a), .o(o)); endmodule\n")

    def overrides(self, p, q):
        env = extract_sym(self.SRC % (p, q), "top")
        inst = [g for g in module(env)["generates"] if g.get("kind") == "Instance"][0]
        return {x["name"]: x["expr"] for x in inst["params"]}

    def test_typed_arithmetic_override_is_loud(self):
        ov = self.overrides("U + 8'd100", "U + 8'd100")
        self.assertEqual(ov["P"]["kind"], "Unsupported")
        self.assertEqual(ov["P"]["sv_kind"], "InstanceSymbol:override-context")
        self.assertEqual(ov["Q"]["sv_kind"], "InstanceSymbol:override-context")

    def test_leaf_select_comparison_and_int_overrides_stay(self):
        ov = self.overrides("U", "U > 8'd5")
        # The leaf is widened into the 16-bit P (zero extension, exact).
        self.assertEqual(strip(ov["P"]),
                         {"kind": "Resize", "operand": {"kind": "ParamRef", "name": "U"}})
        self.assertNotEqual(ov["Q"].get("kind"), "Unsupported")
        self.assertEqual(strip(ov["R"])["kind"], "Binary")


if __name__ == "__main__":
    unittest.main()
