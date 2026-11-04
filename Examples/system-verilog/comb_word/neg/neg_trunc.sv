// WP-B2 negative: a sum into a NARROWER target. The sum is formed at the operand width and then truncated (slang's
// conversion wraps the whole sum, not the operands): outside the fragment.
module neg_trunc #(parameter int N = 4) (input logic [N-1:0] a, b, output logic [N-2:0] y);
  assign y = a + b;
endmodule
