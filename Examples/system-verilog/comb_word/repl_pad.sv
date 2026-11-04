// WP-B2 gate 4c: zero padding, `{ {K{1'b0}}, x }` (a replication of a sized literal, count a parameter, as a part of
// a concatenation): the zero extension of `x` by `K` bits, for every `N` and `K`.
module repl_pad #(parameter int N = 4, parameter int K = 3) (
  input  logic [N-1:0] x,
  output logic [N+K-1:0] y
);
  assign y = { {K{1'b0}}, x };
endmodule
