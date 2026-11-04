"""Round 6 folds (sv-0.2 symbolic mode, 2026-10-29): values and widths the
envelope used to carry at the DEFAULT point only, now refused by the
extractor where the family's points can differ.

1. A parameter/localparam whose declared type is NAMED (a typedef) and whose
   width depends on the point: the type syntax carries no dimensions, so the
   envelope held slang's elaborated bounds — the default point's — and Lean
   read the constant at that width everywhere (round 5 FOLDS verifier
   blocker 2, repros `vs_td2`, `vs_td4`). It is now `packed: null`
   ("unrecoverable packed dimensions"). A fixed-width typedef, and any
   typedef in a family with one point, keeps its bounds.
2. A reference to a member of an enum whose member VALUES depend on the
   point (`EnumValueSymbol:default-point-value`): the EnumType node carries
   each member's default-point value. Fixed enums and package enums stay.
3. An INT-class override with + - * ** into an UNTYPED child parameter
   (`InstanceSymbol:override-untyped-width`): Icarus 12.0 gives the child
   parameter the lossless width (33 bits for `N + 1`), slang and Yosys 0.53
   32. Leaf overrides and overrides into typed parameters stay.
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


def kinds(node):
    found = []

    def walk(n):
        if isinstance(n, dict):
            if n.get("kind") == "Unsupported":
                found.append(n.get("sv_kind"))
            for v in n.values():
                walk(v)
        elif isinstance(n, list):
            for v in n:
                walk(v)
    walk(node)
    return found


TYPEDEFS = """
module td #(parameter int M = 32) (input logic [3:0] a, output logic [63:0] o);
  typedef logic signed [M-1:0] st_t;
  typedef bit [M-1:0] bt_t;
  typedef logic signed [7:0] s8_t;
  typedef bit [7:0] b8_t;
  localparam st_t TS = -1;
  localparam bt_t TB = -1;
  localparam s8_t T8 = -2;
  localparam b8_t B8 = -2;
  assign o = TS + TB + T8 + B8 + a;
endmodule
"""

TYPEDEFS_ONE_POINT = """
module td1 (input logic [3:0] a, output logic [63:0] o);
  localparam int M = 32;
  typedef logic signed [M-1:0] st_t;
  localparam st_t TS = -1;
  assign o = TS + a;
endmodule
"""


class NamedParameterTypes(unittest.TestCase):
    def test_point_dependent_typedef_is_unrecoverable(self):
        ps = params(extract_sym(TYPEDEFS, "td"))
        self.assertIsNone(ps["TS"]["type"]["packed"])
        self.assertIsNone(ps["TB"]["type"]["packed"])

    def test_fixed_typedef_keeps_its_bounds(self):
        ps = params(extract_sym(TYPEDEFS, "td"))
        for name in ("T8", "B8"):
            dims = ps[name]["type"]["packed"]
            self.assertEqual([(d["msb"]["value"], d["lsb"]["value"]) for d in dims],
                             [(7, 0)])

    def test_single_point_family_keeps_the_exact_width(self):
        ps = params(extract_sym(TYPEDEFS_ONE_POINT, "td1"))
        dims = ps["TS"]["type"]["packed"]
        self.assertEqual([(d["msb"]["value"], d["lsb"]["value"]) for d in dims],
                         [(31, 0)])


ENUMS = """
package ep;
  localparam int BASE = 4;
  typedef enum logic [7:0] {PA = BASE, PB = BASE + 1} p_t;
endpackage
module en #(parameter int N = 3) (input logic [3:0] a,
                                  output logic [7:0] o1, o2, o3);
  typedef enum logic [7:0] {EA = N, EB = N + 2} e_t;
  typedef enum logic [N+4:0] {FA = 2, FB, FC = 2 + 3} f_t;
  assign o1 = EB;
  assign o2 = FB + a;
  assign o3 = ep::PB;
endmodule
"""


class EnumMemberValues(unittest.TestCase):
    def test_point_dependent_member_is_refused(self):
        env = extract_sym(ENUMS, "en")
        procs = env["design"]["modules"][0]["processes"]
        self.assertEqual(kinds(procs[0]), ["EnumValueSymbol:default-point-value"])

    def test_fixed_and_package_members_stay(self):
        env = extract_sym(ENUMS, "en")
        procs = env["design"]["modules"][0]["processes"]
        # Round 7 folds: `f_t`'s BASE width depends on the point
        # (`logic [N+4:0]`), so its members are refused too, a recorded
        # over-refusal (FB is 3 wherever it fits; test_sym_folds7.py).
        self.assertEqual(kinds(procs[1]), ["EnumValueSymbol:default-point-value"])
        self.assertEqual(kinds(procs[2]), [])


OVERRIDES = """
module uc #(parameter W = 8, parameter int V = 3, parameter logic [39:0] T = 0)
  (input logic [3:0] a, output logic [63:0] o);
  assign o = {a, W} + V + T;
endmodule
module uo #(parameter int N = 8) (input logic [3:0] a, output logic [63:0] o1, o2, o3, o4);
  uc #(.W(N + 1)) u1 (.a(a), .o(o1));
  uc #(.W(N)) u2 (.a(a), .o(o2));
  uc #(.V(N + 1), .T(N * 2)) u3 (.a(a), .o(o3));
  uc #(.W(N / 2)) u4 (.a(a), .o(o4));
endmodule
"""


class UntypedChildOverrides(unittest.TestCase):
    def overrides(self):
        env = extract_sym(OVERRIDES, "uo")
        top = [m for m in env["design"]["modules"] if m["name"] == "uo"][0]
        return {g["name"]: g for g in top["generates"]}

    def test_widening_override_into_untyped_child_is_refused(self):
        self.assertEqual(kinds(self.overrides()["u1"]["params"]),
                         ["InstanceSymbol:override-untyped-width"])

    def test_leaf_typed_and_non_widening_overrides_stay(self):
        ov = self.overrides()
        self.assertEqual(kinds(ov["u2"]["params"]), [])
        self.assertEqual(kinds(ov["u3"]["params"]), [])
        self.assertEqual(kinds(ov["u4"]["params"]), [])


if __name__ == "__main__":
    unittest.main()
