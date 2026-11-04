// WP-LIN regression design: a chain of nine plain sites at symbolic widths (two windows per vector, so two sites write each of
// x0..x3). It is neither flat (it has parameters) nor small (`groupMinSites` = 4), so `sv_structure` and `sv_equations` take the
// grouped route: the one-driver, rank and cover obligations are asked on the sites that write the same signal only.
module lin_chain #(parameter int W = 5, parameter int P = 11) (
  input  logic [W+P-1:0] a, input logic [W+P-1:0] b, output logic [W+P-1:0] q);
  localparam integer K = W + P;
  localparam integer T = P - 1;
  logic [K-1:0] x0;
  logic [K-1:0] x1;
  logic [K-1:0] x2;
  logic [K-1:0] x3;
  assign x0[T-1:0] = a[T-1:0] ^ b[T-1:0];
  assign x0[K-1:T] = a[K-1:T] ^ b[K-1:T];
  assign x1[T-1:0] = x0[T-1:0] ^ a[T-1:0];
  assign x1[K-1:T] = x0[K-1:T] & a[K-1:T];
  assign x2[T-1:0] = x1[T-1:0] ^ a[T-1:0];
  assign x2[K-1:T] = x1[K-1:T] & a[K-1:T];
  assign x3[T-1:0] = x2[T-1:0] ^ a[T-1:0];
  assign x3[K-1:T] = x2[K-1:T] & a[K-1:T];
  assign q = x3;
endmodule
