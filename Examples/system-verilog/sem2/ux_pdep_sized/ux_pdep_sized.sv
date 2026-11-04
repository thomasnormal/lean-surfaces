// A SIZED x/z literal folded at a parameter-dependent context (round 5
// repair, Lane A, 2026-10-29; verifier repro `vp8`): at the default N = 8
// slang folds `12'hxF0` to the `Literal` `11110000`, which the envelope
// fixed at every point (N = 12, 32, 33, 40, 64: cross-check FAIL "SILENT
// default-point fold"; at N = 40 Icarus 12.0 and the Yosys 0.53 netlist
// give 28 zeros then xxxx11110000). Now loud (`ConversionExpression:
// xz-literal-parametric`). y1 and y2 (0/1 literals, a `Resize`) were
// exact; the module is refused as a whole.
module ux_pdep_sized #(parameter int N = 8) (
  input  logic clk,
  input  logic [7:0] a,
  output logic [N-1:0] y1,
  output logic [N-1:0] y2,
  output logic [N-1:0] y3,
  output logic [N-1:0] y4
);
  assign y1 = 'h1FF;
  assign y2 = 12'hFFF;
  assign y3 = 12'hxF0;
  assign y4 = 'hx0;
endmodule
