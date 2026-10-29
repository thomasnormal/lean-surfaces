"""Round 7 folds (sv-0.2 symbolic mode, 2026-10-29): the round 6 FOLDS
verifier's findings, refusal-only.

1. A cast whose SIZE (or type) depends on the point, `M'(255)`, inside a
   localparam initializer or an instance override: slang binds the size
   away, the operand has no bound name, and the extractor emitted slang's
   DEFAULT-point fold (`ConversionExpression:default-point-fold` now; repros
   `vw_szc2`, `vw_szc3`, `vw_szo`).
2. Enum members: an initializer with an unbased-unsized literal (`'1`,
   `~'0`) is refused at every point and in every scope
   (`EnumValueSymbol:unsized-literal-member`: Icarus 12.0 and the Yosys 0.53
   netlist read `'1` as 1, slang and IEEE 1800-2023 5.7.1 fill it), and an
   enum whose BASE width depends on the point is refused
   (`EnumValueSymbol:default-point-value`; repro `vw_enw`).
3. An INT-class LEFT shift override into an untyped child parameter
   (`.W(1 << N)`): Icarus widens `<<` by the shift amount
   (`InstanceSymbol:override-untyped-width`; repro `vw_sho`).
"""
import unittest

from test_sym_folds6 import extract_sym, kinds


def lp_kinds(env, module=0):
    out = {}
    for item in env["design"]["modules"][module]["params"]:
        if item.get("kind") == "LocalParam":
            out[item["name"]] = kinds(item["expr"])
    return out


SIZE_CASTS = """
module sc #(parameter int M = 8) (input logic [3:0] a, output logic [63:0] o);
  typedef logic [M-1:0] ut_t;
  localparam int X1 = M'(255);
  localparam int X5 = M'(-1);
  localparam int R3 = M'(1) << 3;
  localparam int R4 = signed'(M'(200));
  localparam int R5 = $signed(M'(8'd200));
  localparam int R7 = (M)'(255);
  localparam int R8 = (M + 0)'(255);
  localparam logic [63:0] R9 = M'(255);
  localparam int R11 = M'(200) + 1;
  localparam int T1 = 8'(255);
  localparam int T2 = -1;
  localparam int T3 = 8'sd5 + 8'sd2;
  assign o = X1 + a;
endmodule
"""

SIZE_CASTS_ONE_POINT = """
module sc1 (input logic [3:0] a, output logic [63:0] o);
  localparam int M = 8;
  localparam int X1 = M'(255);
  assign o = X1 + a;
endmodule
"""

SIZE_CAST_OVERRIDES = """
module sc_c #(parameter int W = 0) (input logic [3:0] a, output logic [63:0] o);
  assign o = W + a;
endmodule
module sco #(parameter int M = 8) (input logic [3:0] a, output logic [63:0] o1, o2, o3);
  sc_c #(.W(M'(255))) u1 (.a(a), .o(o1));
  sc_c #(.W(M'(300) + 1)) u2 (.a(a), .o(o2));
  sc_c #(.W(8'(255))) u3 (.a(a), .o(o3));
endmodule
"""


class PointDependentCasts(unittest.TestCase):
    def test_parameter_sized_casts_are_refused(self):
        ks = lp_kinds(extract_sym(SIZE_CASTS, "sc"))
        for name in ("X1", "X5", "R3", "R4", "R5", "R7", "R8", "R9", "R11"):
            self.assertIn("ConversionExpression:default-point-fold", ks[name], name)

    def test_fixed_casts_and_signed_constants_are_unchanged(self):
        ks = lp_kinds(extract_sym(SIZE_CASTS, "sc"))
        for name in ("T1", "T2", "T3"):
            self.assertNotIn("ConversionExpression:default-point-fold", ks[name], name)

    def test_single_point_family_keeps_the_fold(self):
        ks = lp_kinds(extract_sym(SIZE_CASTS_ONE_POINT, "sc1"))
        self.assertEqual(ks["X1"], [])

    def test_parameter_sized_cast_overrides_are_refused(self):
        env = extract_sym(SIZE_CAST_OVERRIDES, "sco")
        top = [m for m in env["design"]["modules"] if m["name"] == "sco"][0]
        ov = {g["name"]: g for g in top["generates"]}
        self.assertEqual(kinds(ov["u1"]["params"]), ["ConversionExpression:default-point-fold"])
        self.assertEqual(kinds(ov["u2"]["params"]), ["ConversionExpression:default-point-fold"])
        self.assertNotIn("ConversionExpression:default-point-fold", kinds(ov["u3"]["params"]))


ENUMS = """
package ep7;
  typedef enum logic [3:0] {PA = '1, PB = 0} p_t;
  typedef enum logic [3:0] {QA = 3, QB} q_t;
endpackage
module en7 #(parameter int N = 4) (input logic [3:0] a,
                                   output logic [63:0] o1, o2, o3, o4, o5, o6);
  typedef enum logic [N-1:0] {S0, S1, S2} s_t;
  typedef enum logic [3:0] {FA = ~'0, FB = 2} f_t;
  typedef enum logic [7:0] {GA = 2, GB} g_t;
  typedef enum logic [3:0] {KA = '0, KB} k_t;
  assign o1 = S1;
  assign o2 = FB;
  assign o3 = ep7::PB;
  assign o4 = ep7::QB;
  assign o5 = GB;
  assign o6 = KB;
endmodule
module en7one (input logic [3:0] a, output logic [63:0] o1);
  typedef enum logic [3:0] {EA = '1, EB = 0} e_t;
  assign o1 = {a, EB};
endmodule
"""


class EnumMemberWidths(unittest.TestCase):
    def procs(self, top):
        env = extract_sym(ENUMS, top)
        mod = [m for m in env["design"]["modules"] if m["name"] == top][0]
        return mod["processes"]

    def test_point_dependent_base_is_refused(self):
        self.assertEqual(kinds(self.procs("en7")[0]), ["EnumValueSymbol:default-point-value"])

    def test_unsized_member_initializers_are_refused_everywhere(self):
        ps = self.procs("en7")
        for i in (1, 2, 5):
            self.assertEqual(kinds(ps[i]), ["EnumValueSymbol:unsized-literal-member"], i)
        self.assertEqual(kinds(self.procs("en7one")[0]),
                         ["EnumValueSymbol:unsized-literal-member"])

    def test_fixed_literal_enums_stay(self):
        ps = self.procs("en7")
        self.assertEqual(kinds(ps[3]), [])
        self.assertEqual(kinds(ps[4]), [])


SHIFT_OVERRIDES = """
module so_c #(parameter W = 8, parameter int V = 0) (input logic [3:0] a, output logic [79:0] o);
  assign o = {a, W} + V;
endmodule
module so #(parameter int N = 8) (input logic [3:0] a, output logic [79:0] o1, o2, o3);
  so_c #(.W(1 << N)) u1 (.a(a), .o(o1));
  so_c #(.W(256 >> N)) u2 (.a(a), .o(o2));
  so_c #(.V(1 << N)) u3 (.a(a), .o(o3));
endmodule
"""


class LeftShiftOverrides(unittest.TestCase):
    def test_left_shift_into_untyped_child_is_refused(self):
        env = extract_sym(SHIFT_OVERRIDES, "so")
        top = [m for m in env["design"]["modules"] if m["name"] == "so"][0]
        ov = {g["name"]: g for g in top["generates"]}
        self.assertEqual(kinds(ov["u1"]["params"]), ["InstanceSymbol:override-untyped-width"])
        self.assertEqual(kinds(ov["u2"]["params"]), [])
        self.assertNotIn("InstanceSymbol:override-untyped-width", kinds(ov["u3"]["params"]))


if __name__ == "__main__":
    unittest.main()
