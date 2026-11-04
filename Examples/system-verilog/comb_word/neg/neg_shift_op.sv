// WP-B2 gate 3 negative: a shift whose left operand is an operation (the fragment takes a signal access, a literal
// or a concatenation there; the operand is written into a signal first).
module neg_shift_op #(parameter int N = 4) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  assign y = (a + b) << 1;
endmodule
