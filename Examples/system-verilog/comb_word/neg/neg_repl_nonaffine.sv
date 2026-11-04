// WP-B2 gate 4c: a replication count that is a product of two parameters (not affine) is refused. (The target is
// declared with a fixed width equal to N*M at the defaults, so no width conversion hides the replication.)
module neg_repl_nonaffine #(parameter int N = 2, parameter int M = 4) (
  input  logic [N-1:0] a,
  output logic [7:0] y
);
  assign y = {N*M{a[0]}};
endmodule
