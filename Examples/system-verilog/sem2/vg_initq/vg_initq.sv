// An initialized OUTPUT variable port, one bit written by always_ff
// (2026-10-28, round 3 CX repair; round-2 WP2 verifier probe `vg_initq`).
// The initializer sits on the port symbol, not on its internal variable,
// and the symbolic extractor used to drop it: `name.sem` read y = x1 where
// Icarus reads 11 (§10.5: the initializer is the variable's initial value).
// Since round 4 (Lane A) the always_ff block is REFUSED
// (`ProceduralBlockSymbol:initialized-variable`): Xcelium 24.03 rejects the
// design (`*E,MULAXX: Multiple drivers to always_ff output variable y`)
// where Icarus 12.0, Verilator 5.042, Yosys 0.53 and slang run it. The
// initializer itself is still emitted (`pi_ansi_forms` pins it with a
// plain `always` writer).
module vg_initq (
  input  logic clk,
  input  logic a,
  output logic [1:0] y = 2'b10
);
  always_ff @(posedge clk) y[0] <= a;
endmodule
