// WP-B2 gate 3 negative: a shift whose amount is an expression (the fragment takes a signal access, a sized
// literal or an unsized constant as the amount).
module neg_shift_amt #(parameter int N = 4) (input logic [N-1:0] a, input logic [2:0] s, output logic [N-1:0] y);
  assign y = a << (s + 3'd1);
endmodule
