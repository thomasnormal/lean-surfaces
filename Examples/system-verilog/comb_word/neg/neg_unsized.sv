// WP-B2 negative: an unsized constant operand (a 32-bit operand: the sum is formed at 32 bits and truncated).
module neg_unsized #(parameter int N = 4) (input logic [N-1:0] a, output logic [N-1:0] y);
  assign y = a + 1;
endmodule
