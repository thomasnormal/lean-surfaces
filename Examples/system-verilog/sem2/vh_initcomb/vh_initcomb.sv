// A child's initialized output port written by `always_comb` (2026-10-28,
// round 4 Lane A): `vg_initc` inside a hierarchy. Xcelium 24.03 rejects it
// (`xmelab: *E,MULAXX: Multiple drivers to always_comb output variable o`)
// where Icarus 12.0, Yosys 0.53 and slang run it: the tools split, so the
// block is refused (`ProceduralBlockSymbol:initialized-variable`).
module vh_initcomb_c (
  input  logic       a,
  output logic [1:0] o = 2'b10
);
  always_comb o[0] = a;
endmodule

module vh_initcomb (
  input  logic       a,
  output logic [1:0] y
);
  vh_initcomb_c u (.a(a), .o(y));
endmodule
