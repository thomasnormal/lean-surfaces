// WP-G S2 negative: an unbased unsized fill inside a conditional arm (a follow-up; write a sized literal).
module neg_fill #(parameter int N = 4) (input logic [N-1:0] a, input logic s, output logic [N-1:0] y);
  assign y = s ? a : '0;
endmodule
