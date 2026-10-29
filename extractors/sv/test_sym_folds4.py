"""Round 4 folds: a genvar initializer is an assignment to the genvar's
32-bit `integer` (sv-0.2 symbolic mode, 2026-10-28).

slang binds `genvar g = U + 1'b1` as an `Implicit` conversion to `integer`
around the operand tree. Where that tree has 32 bits at the DEFAULT point
the conversion changes no bit and the generic path dropped it, so the
envelope held the bare tree, which the Lean constant tier evaluated at its
OWN width at every other point: Icarus 12.0's reading, while slang's own
elaboration, the Yosys 0.53 netlist and IEEE 1800-2023 10.8/11.8.1 use 32
bits (verifier repro `rf_gv`: 0 against 16 at N = 4). `_sym_genvar_init`
keeps the assignment as `Resize(32, init)` (`SignedResize` for a signed
operand), which Lean reads as an assignment-like root: the own-width value
where the two readings agree, `Constant:assignment-context` where they
differ or where the value does not fit the 32-bit target.

INT-class initializers at EVERY point (`_sym_genvar_int_class`: unsized
integers, genvars, `int`/`integer` parameters, untyped parameters with an
INT default) are unchanged — a `logic signed [N-1:0]` parameter is 32 bits
only at N = 32 and is not of the class.
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
                if k not in ("span", "resolved_width", "signed")}
    if isinstance(node, list):
        return [strip(v) for v in node]
    return node


def inits(source, top):
    env = extract_sym(source, top)
    return {g["label"]: strip(g["init"])
            for g in env["design"]["modules"][0]["generates"]
            if g.get("kind") == "GenerateFor"}


SOURCE = """
module gi #(parameter int N = 32, parameter integer I = 3, parameter P = 5,
            parameter logic [N-1:0] U = 3, parameter logic signed [N-1:0] S = 1,
            parameter logic signed [3:0] T = 1, parameter Q = 4'd3) (
  input logic a, output logic [9:0] o);
  for (genvar g = N - 1; g < N; g++) begin : A assign o[0] = a; end
  for (genvar g = I + P; g < 9; g++) begin : B assign o[1] = a; end
  for (genvar g = U + 1'b1; g < 5; g++) begin : C assign o[2] = a; end
  for (genvar g = S + S; g < 3; g++) begin : D assign o[3] = a; end
  for (genvar g = T + T; g < 3; g++) begin : E assign o[4] = a; end
  for (genvar g = Q; g < 4; g++) begin : F assign o[5] = a; end
  for (genvar g = U; g < 4; g++) begin : G assign o[6] = a; end
  for (genvar g = 0; g < 1; g++) begin : H assign o[7] = a; end
endmodule
"""


class GenvarInitTarget(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.inits = inits(SOURCE, "gi")

    def test_int_class_initializers_are_unchanged(self):
        self.assertEqual(self.inits["A"]["kind"], "Binary")
        self.assertEqual(self.inits["B"],
                         {"kind": "Binary", "width": 32, "op": "+",
                          "left": {"kind": "ParamRef", "name": "I"},
                          "right": {"kind": "ParamRef", "name": "P"}})
        self.assertEqual(self.inits["H"], {"kind": "Int", "value": 0})

    def test_unsigned_operand_is_kept_under_resize(self):
        c = self.inits["C"]
        self.assertEqual(c["kind"], "Resize")
        self.assertEqual(c["width"], 32)
        self.assertEqual(c["operand"]["kind"], "Binary")
        self.assertEqual(c["operand"]["left"], {"kind": "ParamRef", "name": "U"})
        g = self.inits["G"]
        self.assertEqual(g, {"kind": "Resize", "width": 32,
                             "operand": {"kind": "ParamRef", "name": "U"}})

    def test_signed_operand_of_a_ranged_parameter_is_kept_under_signed_resize(self):
        # `logic signed [N-1:0] S` is 32 bits at the default only: no root
        # conversion in slang's tree, yet not of the INT class.
        d = self.inits["D"]
        self.assertEqual(d["kind"], "SignedResize")
        self.assertEqual(d["width"], 32)
        self.assertEqual(d["operand"]["op"], "+")
        e = self.inits["E"]
        self.assertEqual(e["kind"], "SignedResize")
        self.assertEqual(e["operand"]["left"]["kind"], "SignedResize")

    def test_narrow_untyped_parameter_is_wrapped(self):
        f = self.inits["F"]
        self.assertEqual(f["kind"], "Resize")
        self.assertEqual(f["operand"]["kind"], "Resize")
        self.assertEqual(f["operand"]["operand"], {"kind": "ParamRef", "name": "Q"})


if __name__ == "__main__":
    unittest.main()


OVR_SOURCE = """
module ovc #(parameter logic signed [39:0] P = 0, parameter logic [39:0] Q = 0,
             parameter int R = 0, parameter logic [15:0] T = 0) (
  output logic [39:0] o1, output logic [39:0] o2, output logic [31:0] o3, output logic [15:0] o4);
  assign o1 = P; assign o2 = Q; assign o3 = R; assign o4 = T;
endmodule
module ov #(parameter int N = 5, parameter logic signed [N-1:0] S = 1) (
  output logic [39:0] o1, output logic [39:0] o2, output logic [31:0] o3, output logic [15:0] o4);
  ovc #(.P(N * 1024), .Q(N + 1), .R(N + 2), .T(S + 1)) c (.o1(o1), .o2(o2), .o3(o3), .o4(o4));
endmodule
"""


class WideIntOverride(unittest.TestCase):
    """An INT-class override into a typed parameter wider than 32 bits keeps
    the assignment as a root conversion of the parameter's width; one into
    a 32-bit parameter is unchanged; a point-dependent signed leaf is not of
    the INT class (the typed propagating override is refused)."""

    @classmethod
    def setUpClass(cls):
        env = extract_sym(OVR_SOURCE, "ov")
        cls.params = {}
        def walk(node):
            if isinstance(node, dict):
                if node.get("kind") == "Instance":
                    for p in node["params"]:
                        cls.params[p["name"]] = strip(p["expr"])
                for v in node.values():
                    walk(v)
            elif isinstance(node, list):
                for v in node:
                    walk(v)
        walk(env)

    def test_wide_targets_keep_a_root_conversion(self):
        for name in ("P", "Q"):
            node = self.params[name]
            self.assertEqual(node["kind"], "SignedResize")
            self.assertEqual(node["width"], 40)
            self.assertEqual(node["operand"]["kind"], "Binary")

    def test_32_bit_target_is_unchanged(self):
        self.assertEqual(self.params["R"]["kind"], "Binary")

    def test_point_dependent_signed_leaf_is_refused(self):
        self.assertEqual(self.params["T"]["kind"], "Unsupported")
        self.assertEqual(self.params["T"]["sv_kind"], "InstanceSymbol:override-context")
