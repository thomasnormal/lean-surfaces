// WP-B2 negative: a shift.
module neg_shift #(parameter int N = 4) (input logic [N-1:0] a, output logic [N-1:0] y);
  assign y = a << 1;
endmodule
