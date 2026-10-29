// The parametric twin of `ux_expr` (2026-10-28, round 4 repair): `'hz1`
// widened into `[N-1:0]`. The padded value depends on the context width,
// and the literal's own 32 bits take part in sizing its expression, so no
// symbolic form is exact at every point: loud
// (`ConversionExpression:unsized-xz`). Icarus 12.0 and Xcelium 24.03 give
// y = 36 z then 0001 at N = 40 and zzzz0001 at N = 8 for a = 1.
module ux_expr_p #(
  parameter int N = 40
) (
  input  logic         clk,
  input  logic         a,
  output logic [N-1:0] y
);
  assign y = a ? 'hz1 : 'b0;
endmodule
