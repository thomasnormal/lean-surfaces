// The parametric twin of `pi_unsized_xz` (2026-10-28, round 4 repair): `y`
// has a fixed width inside the family (padded literal); `f`, `g` and `t`
// are unsized literals of ONE repeated x/z bit at a parameter-dependent
// width, emitted as `Fill` (the initializer is the whole expression, so
// truncation and §5.7.1 extension both give that bit everywhere). Icarus
// 12.0, Xcelium 24.03 and the Yosys 0.53 netlist agree at N = 1, 4, 8, 40.
module pi_unsized_xz_p #(
  parameter int N = 4
) (
  input  logic          clk,
  input  logic          a,
  output logic [39:0]   y = 'hz1,
  output logic [N-1:0]  f = 'bx,
  output logic [N+35:0] g = 'hz,
  output logic [N-1:0]  h
);
  logic [N-1:0] t = 'bz;
  always @(posedge clk) f[0] <= a;
  assign h = t;
endmodule
