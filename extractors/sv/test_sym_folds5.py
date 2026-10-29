"""Round 5 folds (sv-0.2 symbolic mode, 2026-10-28): what the extractor
records so that a parameter's TYPE is exact at every point.

1. `signed` on every parameter/localparam whose declared width depends on a
   parameter. The field used to be emitted only where the type departed
   from "signed exactly when 32 bits wide" at the DEFAULT point, and the
   Lean constant tier applies that rule at each point's width: `logic
   signed [M-1:0] S` (default M = 32) was read unsigned at M = 8, `logic
   [N-1:0] U` (default N = 8) signed at N = 32 (verifier repros `vq_sgn2`,
   `vq_sgn3`). Fixed-width types keep the old encoding.
2. An INT-class context-propagating instance override into a child
   parameter whose declared type depends on a parameter is refused
   (`InstanceSymbol:override-context`): the override's root conversion
   carries the child's width at the DEFAULT point only (verifier repro
   `vq_ovr2`: `.W(N + 40), .P(N << 40)` is -2^40 at N = 1 in Icarus 12.0
   and 0 in the Yosys 0.53 netlist, both readings of the default 40 bits
   are 0). Leaves and fixed-width children stay admitted.
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


def params(env, module=0):
    return {p["name"]: p for p in env["design"]["modules"][module]["params"]}


SIGNS = """
module sg #(parameter int M = 32, parameter logic signed [M-1:0] S = -1,
            parameter int N = 8, parameter logic [N-1:0] U = -1,
            parameter logic [31:0] F = 0, parameter logic signed [7:0] G = 0,
            parameter int unsigned UI = 0, parameter integer I = 0) (
  output logic [63:0] o);
  localparam logic signed [M-1:0] LS = S;
  localparam logic [N-1:0] LU = U;
  localparam logic [7:0] LF = 3;
  assign o = S + U + LS + LU + LF + F + G + UI + I;
endmodule
"""


class DeclaredSignedness(unittest.TestCase):
    def test_parameter_dependent_types_always_carry_signed(self):
        ps = params(extract_sym(SIGNS, "sg"))
        # S is 32 bits at the default point, where "signed iff 32" held.
        self.assertIs(ps["S"].get("signed"), True)
        self.assertIs(ps["LS"].get("signed"), True)
        # U is 8 bits at the default point, where "unsigned" held.
        self.assertIs(ps["U"].get("signed"), False)
        self.assertIs(ps["LU"].get("signed"), False)

    def test_fixed_width_types_keep_the_default_rule(self):
        ps = params(extract_sym(SIGNS, "sg"))
        self.assertNotIn("signed", ps["M"])
        self.assertNotIn("signed", ps["I"])
        self.assertNotIn("signed", ps["LF"])
        self.assertIs(ps["F"].get("signed"), False)
        self.assertIs(ps["G"].get("signed"), True)
        self.assertIs(ps["UI"].get("signed"), False)


OVERRIDES = """
module ch #(parameter int W = 40, parameter logic signed [W-1:0] P = 0,
            parameter logic signed [39:0] Q = 0, parameter int R = 0,
            parameter logic [4*10-1:0] E = 0, parameter X = 0,
            parameter logic [$clog2(W):0] C = 0) (output logic [63:0] o);
  assign o = P + Q + R + E + X + C;
endmodule
module top #(parameter int N = 0) (output logic [63:0] o1, o2, o3);
  ch #(.W(N + 40), .P(N << 40)) u1 (.o(o1));
  ch #(.W(N + 40), .P(N), .Q(N << 3), .R(N - 1), .E(N + 1), .X(N * 2),
       .C(N + 1)) u2 (.o(o2));
  ch #(.W(40), .P(N * 2048)) u3 (.o(o3));
endmodule
"""


def overrides(env):
    out = {}
    for g in env["design"]["modules"][0]["generates"]:
        if g.get("kind") == "Instance":
            out[g["name"]] = {p["name"]: p["expr"] for p in g["params"]}
    return out


class OverrideIntoDependentType(unittest.TestCase):
    def test_propagating_override_into_dependent_type_is_refused(self):
        ov = overrides(extract_sym(OVERRIDES, "top"))
        self.assertEqual(ov["u1"]["P"]["kind"], "Unsupported")
        self.assertEqual(ov["u1"]["P"]["sv_kind"], "InstanceSymbol:override-context")
        # A propagating override of a dependent type ALSO refuses in u2.
        self.assertEqual(ov["u2"]["C"]["kind"], "Unsupported")

    def test_leaves_and_fixed_types_stay_admitted(self):
        ov = overrides(extract_sym(OVERRIDES, "top"))
        u2 = ov["u2"]
        self.assertNotEqual(u2["P"]["kind"], "Unsupported")  # a leaf
        self.assertEqual(u2["Q"]["kind"], "SignedResize")     # fixed 40 bits
        self.assertEqual(u2["Q"]["width"], 40)
        self.assertEqual(u2["R"]["kind"], "Binary")           # into an int
        self.assertNotEqual(u2["E"]["kind"], "Unsupported")   # literal bounds
        # Untyped X: round 6 refuses `.X(N * 2)` (Icarus gives the untyped
        # child parameter the lossless 64 bits, slang and Yosys 32 —
        # test_sym_folds6.py); a leaf into it stays admitted there.
        self.assertEqual(u2["X"]["sv_kind"], "InstanceSymbol:override-untyped-width")
        self.assertNotEqual(u2["W"]["kind"], "Unsupported")
        # `.W(40)`: the dependent type has one width at every point, so the
        # override keeps round 4's root conversion of that width.
        self.assertEqual(ov["u3"]["P"]["kind"], "SignedResize")
        self.assertEqual(ov["u3"]["P"]["width"], 40)

    def test_fixed_type_predicate(self):
        env = {}
        src = OVERRIDES
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "f.sv"
            path.write_text(src)
            import pyslang
            from pyslang.ast import Compilation
            from pyslang.syntax import SyntaxTree
            comp = Compilation()
            comp.addSyntaxTree(SyntaxTree.fromFile(str(path)))
            inst = [t for t in comp.getRoot().topInstances if t.name == "top"][0]
            for m in inst.body:
                if type(m).__name__ == "InstanceSymbol":
                    for p in m.body.parameters:
                        env[p.name] = extract._sym_param_type_fixed(p)
                    break
        self.assertEqual(env, {"W": True, "P": False, "Q": True, "R": True,
                               "E": True, "X": True, "C": False})


if __name__ == "__main__":
    unittest.main()
