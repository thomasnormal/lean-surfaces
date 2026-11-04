// WP-G S2 negative: an ordering comparison is a word-level operator.
module neg_cmp #(parameter int N = 4) (input logic [N-1:0] a, b, output logic y);
  assign y = a > b;
endmodule
