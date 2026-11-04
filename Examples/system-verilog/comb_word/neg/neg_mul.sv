// WP-B2 negative: `*` is not in the fragment.
module neg_mul #(parameter int N = 4) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  assign y = a * b;
endmodule
