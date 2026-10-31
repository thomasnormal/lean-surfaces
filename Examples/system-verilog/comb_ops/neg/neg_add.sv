// WP-G S2 negative: arithmetic is a word-level operator, outside the second fragment (B2).
module neg_add #(parameter int N = 4) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  assign y = a + b;
endmodule
