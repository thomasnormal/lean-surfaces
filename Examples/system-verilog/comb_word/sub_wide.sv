// WP-B2: `a - b` into a target one bit wider: the operands are zero-extended first (not sign-extended), the
// difference wraps modulo 2^(N+1), and d[N] is the borrow.
module sub_wide #(parameter int N = 8) (
  input  logic [N-1:0] a, b,
  output logic [N:0]   d
);
  assign d = a - b;
endmodule
