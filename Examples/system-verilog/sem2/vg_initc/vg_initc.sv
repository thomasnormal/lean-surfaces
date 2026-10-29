// A declaration initializer plus an always_comb writer of one bit
// (2026-10-28, round 3 CX repair; round-2 WP2 verifier probe `vg_initc`).
// Round 3 admitted it as legal; round 4 (Lane A) REFUSES it: Xcelium 24.03
// rejects the design (`xmelab: *E,MULAXX: Multiple drivers to always_comb
// output variable t`; IEEE 1800-2023 §9.2.2.2 lets no other process assign
// an always_comb variable, and §6.5/§10.5 count the initialization as a
// procedural assignment) where Icarus 12.0, Verilator 5.042, Yosys 0.53 and
// slang run it. The tools split, so the block is loud
// (`ProceduralBlockSymbol:initialized-variable`).
module vg_initc (
  input  logic a,
  output logic [1:0] y
);
  logic [1:0] t = 2'b10;
  always_comb t[0] = a;
  assign y = t;
endmodule
