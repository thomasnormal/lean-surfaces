// An x-bit literal initializer with no conversion at the default point, at a
// parameter-dependent width (2026-10-28, round 4 repair, INIT verifier
// `w_lit2x`): the 2-bit `Literal` was stored unchanged at every point (2
// bits at N = 4, where Icarus 12.0, Xcelium 24.03 and the Yosys 0.53
// netlist give 00x1). A sized x literal is zero-extended at each width, which
// no symbolic initializer expresses: loud
// (`Initializer:x-literal-parametric-width`, "non-literal initializer").
module pi_lit_px #(
  parameter int N = 2
) (
  input  logic         clk,
  input  logic         a,
  output logic [N-1:0] y = 2'bx1
);
  always @(posedge clk) y[0] <= a;
endmodule
