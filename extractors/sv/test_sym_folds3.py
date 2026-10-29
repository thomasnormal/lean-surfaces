"""Round 3 default-point folds (sv-0.2 symbolic mode, 2026-10-28).

(1) A signed parameter / localparam / genvar reference propagated into an
UNSIGNED context of its own width at the default point (`a + P`, `int P`,
9-bit `a`) keeps slang's conversion as `Resize(width, ParamRef)`: Lean then
zero-extends it from its own width wherever the context is wider (IEEE
1800-2023 §11.8.2), where the bare `ParamRef` was sign-extended. Only in a
parametric family, only `Propagated` conversions (an assignment-like one
keeps the right-hand side's signedness), only parameter/genvar operands.

(2) A select whose ROOT is a parameter value keeps the legacy encoding only
where its labels are offsets at every point: a range canonical `[m:0]` at
the default point (Lean checks it per point), or literal bounds with folded
offsets (not an indexed part select). Anything else is
`<kind>:param-range`.

(5) A NON-ANSI output port whose variable is declared separately with an
initializer carries that initializer (`init`), as the ANSI form does.
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
        return {k: strip(v) for k, v in node.items() if k not in ("span", "width", "resolved_width")}
    if isinstance(node, list):
        return [strip(v) for v in node]
    return node


def values(env):
    return {p["target"]["name"]: strip(p["value"])
            for p in env["design"]["modules"][0]["processes"] if p.get("kind") == "Assign"}


class SignedSimpleOperandMarker(unittest.TestCase):
    SRC = ("module top #(parameter int N = 7, parameter int P = -3) "
           "(input logic [N+1:0] a, output logic [N+1:0] o1, o2, o4, output logic o3); "
           "assign o1 = a + P; assign o2 = a & P; assign o3 = (a == P); assign o4 = P; "
           "endmodule\n")

    def test_propagated_param_is_wrapped(self):
        v = values(extract_sym(self.SRC, "top"))
        marker = {"kind": "Resize", "operand": {"kind": "ParamRef", "name": "P"}}
        self.assertEqual(v["o1"]["operand"]["right"], marker)
        self.assertEqual(v["o2"]["operand"]["right"], marker)
        self.assertEqual(v["o3"]["right"], marker)

    def test_assignment_like_conversion_is_unchanged(self):
        # `o4 = P`: an Implicit conversion keeps P's signedness (sign
        # extension) — the unconverted INT-class tree, as before.
        v = values(extract_sym(self.SRC, "top"))
        self.assertEqual(v["o4"], {"kind": "ParamRef", "name": "P"})

    def test_single_point_module_is_unchanged(self):
        src = ("module top (input logic [8:0] a, output logic [8:0] o1); "
               "localparam int P = -3; assign o1 = a + P; endmodule\n")
        v = values(extract_sym(src, "top"))
        self.assertEqual(v["o1"]["operand"]["right"], {"kind": "ParamRef", "name": "P"})

    def test_genvar_is_wrapped(self):
        src = ("module top #(parameter int N = 7) (input logic [N+1:0] a, "
               "output logic [N+1:0] o); "
               "for (genvar g = -1; g < 0; g++) begin : gl assign o = a ^ g; end endmodule\n")
        env = extract_sym(src, "top")
        body = env["design"]["modules"][0]["generates"][0]["body"]
        self.assertEqual(strip(body[0]["value"])["operand"]["right"],
                         {"kind": "Resize", "operand": {"kind": "GenvarRef", "name": "g"}})

    def test_unsized_literal_is_unchanged(self):
        src = ("module top #(parameter int N = 7) (input logic [N+1:0] a, "
               "output logic [N+1:0] o); assign o = a + 5; endmodule\n")
        v = values(extract_sym(src, "top"))
        self.assertEqual(v["o"]["operand"]["right"], {"kind": "Int", "value": 5})


class ParamRootSelects(unittest.TestCase):
    def kinds(self, body, decls=""):
        src = ("module top #(parameter int N = 4) (input logic a, output logic o1, "
               "output logic [1:0] o2); " + decls + body + " endmodule\n")
        return {k: (v.get("sv_kind") or v["kind"]) for k, v in values(extract_sym(src, "top")).items()}

    def test_canonical_symbolic_range_keeps_raw_labels(self):
        src = ("module top #(parameter int N = 4) (input logic a, output logic o1, "
               "output logic [1:0] o2); localparam logic [N-1:0] P = 3; "
               "assign o1 = P[1]; assign o2 = P[0 +: 2]; endmodule\n")
        v = values(extract_sym(src, "top"))
        self.assertEqual(v["o1"]["kind"], "BitSel")
        self.assertEqual(v["o1"]["index"], {"kind": "Int", "value": 1})
        self.assertEqual(v["o2"]["kind"], "PartSel")

    def test_literal_bounds_keep_folded_offsets(self):
        k = self.kinds("assign o1 = Q[5]; assign o2 = Q[6:5];",
                       "localparam logic [7:4] Q = 4'b1010; ")
        self.assertEqual(k, {"o1": "BitSel", "o2": "PartSel"})

    def test_non_canonical_symbolic_range_is_loud(self):
        k = self.kinds("assign o1 = P[2]; assign o2 = Q[1:2];",
                       "localparam logic [N-1:1] P = 3; localparam logic [0:N-1] Q = 4'b1010; ")
        self.assertEqual(k, {"o1": "ElementSelectExpression:param-range",
                             "o2": "RangeSelectExpression:param-range"})

    def test_indexed_select_over_literal_ascending_range_is_loud(self):
        k = self.kinds("assign o2 = R[0 +: 2];", "localparam logic [0:3] R = 4'b0011; ")
        self.assertEqual(k["o2"], "RangeSelectExpression:param-range")

    def test_multi_dimensional_parameter_is_loud(self):
        k = self.kinds("assign o1 = M[1][0];", "localparam logic [1:0][3:0] M = 8'hA5; ")
        self.assertEqual(k["o1"], "ElementSelectExpression:param-range")


class DimensionQueryFolds(unittest.TestCase):
    """`$left`/`$right`/`$low` stay outside the tier; slang folds them at the
    default point, which is exact only over a range written with literal
    bounds (round 3 folds, item 4)."""

    def test_parameter_dependent_range_is_loud(self):
        v = values(extract_sym(
            "module top #(parameter int N = 3) (input logic [N-1:0] v, "
            "output logic [7:0] o1, o2, o3); assign o1 = $left(v); "
            "assign o2 = $right(v); assign o3 = $low(v); endmodule\n", "top"))
        self.assertEqual({k: x.get("sv_kind") for k, x in v.items()},
                         {k: "ConversionExpression:default-point-fold" for k in ("o1", "o2", "o3")})

    def test_literal_range_keeps_the_fold(self):
        v = values(extract_sym(
            "module top #(parameter int N = 3) (input logic [7:4] u, "
            "output logic [7:0] o1, o2); assign o1 = $left(u); "
            "assign o2 = $low(u); endmodule\n", "top"))
        self.assertEqual(v["o1"], {"kind": "Literal", "bits": "00000111"})
        self.assertEqual(v["o2"], {"kind": "Literal", "bits": "00000100"})

    def test_single_point_module_keeps_the_fold(self):
        v = values(extract_sym(
            "module top (input logic [3:0] v, output logic [7:0] o1); "
            "assign o1 = $left(v); endmodule\n", "top"))
        self.assertEqual(v["o1"], {"kind": "Literal", "bits": "00000011"})

    def test_value_position_high_and_size_are_syscalls(self):
        v = values(extract_sym(
            "module top #(parameter int N = 3) (input logic [N-1:0] v, "
            "output logic [7:0] o1, o2); assign o1 = $high(v); "
            "assign o2 = $size(v); endmodule\n", "top"))
        self.assertEqual(v["o1"]["kind"], "SysCall")
        self.assertEqual(v["o2"]["kind"], "SysCall")


class NonAnsiPortInitializer(unittest.TestCase):
    def port(self, src, top="top", name="y"):
        env = extract_sym(src, top)
        for m in env["design"]["modules"]:
            for p in m["ports"]:
                if p.get("name") == name:
                    return p
        raise AssertionError("no port " + name)

    def test_logic_variable(self):
        p = self.port("module top(clk, a, y); input clk; input a; output [1:0] y; "
                      "logic [1:0] y = 2'b10; always_ff @(posedge clk) y[0] <= a; endmodule\n")
        self.assertEqual(p["init"]["kind"], "Literal")

    def test_reg_variable(self):
        p = self.port("module top(clk, a, y); input clk; input a; output [1:0] y; "
                      "reg [1:0] y = 2'b10; always @(posedge clk) y[0] <= a; endmodule\n")
        self.assertEqual(p["init"]["kind"], "Literal")

    def test_parametric_fill(self):
        p = self.port("module top(clk, a, y); parameter int N = 3; input clk; input a; "
                      "output [N-1:0] y; logic [N-1:0] y = '1; "
                      "always_ff @(posedge clk) y[0] <= a; endmodule\n")
        self.assertEqual(p["init"]["kind"], "Fill")

    def test_uninitialized_non_ansi_port_has_no_init(self):
        p = self.port("module top(clk, a, y); input clk; input a; output [1:0] y; "
                      "logic [1:0] y; always_ff @(posedge clk) y <= {a, a}; endmodule\n")
        self.assertNotIn("init", p)

    def test_continuous_driver_of_initialized_non_ansi_port_is_loud(self):
        env = extract_sym("module top(a, y); input a; output [1:0] y; "
                          "logic [1:0] y = 2'b10; assign y[0] = a; endmodule\n", "top")
        procs = env["design"]["modules"][0]["processes"]
        self.assertEqual(procs[0].get("sv_kind"), "ContinuousAssignSymbol:initialized-variable")


if __name__ == "__main__":
    unittest.main()
