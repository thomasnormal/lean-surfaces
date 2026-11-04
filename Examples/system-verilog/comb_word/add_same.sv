// WP-B2: an adder written with `+`. All three signals are N bits wide, so slang puts no conversion around the
// operands and the sum wraps modulo 2^N.
module add_same #(parameter int N = 8) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  assign y = a + b;
endmodule
