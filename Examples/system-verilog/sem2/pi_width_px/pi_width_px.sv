// A literal with an x bit, zero-extended to a PARAMETER-dependent width
// (2026-10-28, round 4 Lane A): the conversion is kept, so the
// initializer stays loud (`instDecl`: non-literal initializer) — the
// extractor lowers x/z literals only at a width fixed at every point.
module pi_width_px #(
  parameter int N = 4
) (
  input  logic         clk,
  input  logic         a,
  output logic [N-1:0] y = 2'bx1
);
  always @(posedge clk) y[N-1] <= a;
endmodule
