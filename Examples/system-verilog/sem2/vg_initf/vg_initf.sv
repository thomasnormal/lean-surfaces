// A declaration initializer plus an `always_ff` writer of one bit
// (2026-10-28, round 4 Lane A; the round-2 WP2 verifier's probe `vg_initf`,
// then admitted). Xcelium 24.03 rejects it (`xmelab: *E,MULAXX: Multiple
// drivers to always_ff output variable t`: IEEE 1800-2023 §9.2.2.4 lets no
// other process assign an always_ff variable, and §6.5/§10.5 count the
// initialization as a procedural assignment) where Icarus 12.0, Verilator
// 5.042, Yosys 0.53 and slang run it: the tools split, so the block is
// refused (`ProceduralBlockSymbol:initialized-variable`).
module vg_initf (
  input  logic       clk,
  input  logic       a,
  output logic [1:0] y
);
  logic [1:0] t = 2'b10;
  always_ff @(posedge clk) t[0] <= a;
  assign y = t;
endmodule
