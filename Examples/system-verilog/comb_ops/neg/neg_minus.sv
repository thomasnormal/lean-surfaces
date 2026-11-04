// WP-G S2 negative: unary minus is arithmetic.
module neg_minus #(parameter int N = 4) (input logic [N-1:0] a, output logic [N-1:0] y);
  assign y = -a;
endmodule
