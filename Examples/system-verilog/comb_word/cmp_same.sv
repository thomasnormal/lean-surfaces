// WP-B2 gate 2b: the six comparisons of two operands of one width (no conversion marker): one bit each.
module cmp_same #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic eq, ne, lt, le, gt, ge
);
  assign eq = a == b;
  assign ne = a != b;
  assign lt = a < b;
  assign le = a <= b;
  assign gt = a > b;
  assign ge = a >= b;
endmodule
