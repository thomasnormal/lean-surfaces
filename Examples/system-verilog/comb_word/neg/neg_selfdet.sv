// WP-B2 negative: a sum in a SELF-determined position (the operand of a reduction).
module neg_selfdet #(parameter int N = 4) (input logic [N-1:0] a, b, output logic y);
  assign y = |(a + b);
endmodule
