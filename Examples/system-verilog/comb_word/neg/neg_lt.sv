// WP-B2 negative: an ordering comparison.
module neg_lt #(parameter int N = 4) (input logic [N-1:0] a, b, output logic y);
  assign y = a < b;
endmodule
