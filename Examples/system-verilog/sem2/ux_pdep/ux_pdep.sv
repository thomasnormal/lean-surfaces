// Unsized x/z literals in a parametric family whose DEFAULT context is
// exactly 32 bits (round 5 repair, Lane A, 2026-10-29; verifier repro
// `vp3`). At the default there is no conversion, so the envelope held a
// 32-bit `Literal` that Lean zero-extended at every wider point: at N = 40
// y1 = 8 zeros, 28 x, 0000, where Icarus 12.0 and the Yosys 0.53 netlist
// give 36 x then 0000 (IEEE 1800-2023 §5.7.1). Now loud
// (`IntegerLiteral:unsized-xz-parametric`, `_sym_xz_literal_scan`).
module ux_pdep #(parameter int N = 32) (
  input  logic clk,
  input  logic [7:0] a,
  output logic [N-1:0] y1,
  output logic [N-1:0] y2,
  output logic [N-1:0] y3
);
  assign y1 = 'hx0;
  assign y2 = 'hz1;
  assign y3 = 'bx;
endmodule
