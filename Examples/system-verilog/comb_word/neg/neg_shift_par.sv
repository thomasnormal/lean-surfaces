// WP-B2 gate 3 negative: a shift by an expression over a PARAMETER (`a << (N - 1)`, likewise `a << N`): the amount is
// not a signal access or a constant, so it is outside the fragment for now (the first candidate for a later gate).
module neg_shift_par #(parameter int N = 4) (input logic [N-1:0] a, output logic [N-1:0] y);
  assign y = a << (N - 1);
endmodule
