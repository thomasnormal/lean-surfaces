// WP-B2 gate 4c: the replicated operand must be a sized literal or one access; an operation is refused.
module neg_repl_op (
  input  logic [3:0] a,
  input  logic [3:0] b,
  output logic [7:0] y
);
  assign y = {2{a & b}};
endmodule
