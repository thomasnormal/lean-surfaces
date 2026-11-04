// `ux_pdep` with a NARROWER default context, N = 8 (round 5 repair, Lane A,
// 2026-10-29; verifier repro `vp6`): slang folds the truncation to a
// default-width `Literal` (`'hx0` -> `xxxx0000`), which Lean zero-extended
// at every wider point (N = 31, 32: cross-check FAIL "SILENT default-point
// fold"; N = 33, 40, 64: FAIL against Icarus 12.0, whose trace equals the
// Yosys 0.53 netlist's). Now loud (`ConversionExpression:xz-literal-
// parametric` and `IntegerLiteral:unsized-xz-parametric`).
module ux_pdep_narrow #(parameter int N = 8) (
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
