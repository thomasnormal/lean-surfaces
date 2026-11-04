// WP-B2 gate 2b: a sum into a narrower target (slang wraps the sum in a truncation marker), and sums with an
// unsized constant (`a + 1` is `Resize[(Resize32[a] + 1)]`: a 32-bit sum, truncated to the target).
module trunc_inc #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-2:0] t,
  output logic [N-1:0] y1,
  output logic [N:0]   y2
);
  assign t = a + b;
  assign y1 = a + 1;
  assign y2 = a - 1;
endmodule
