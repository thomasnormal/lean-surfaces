// WP-B2 gate 2b: comparisons of operands of different widths (slang zero-extends the narrower one: a `Resize`
// marker), against an unsized constant (32 bits wide), and into a wider target (a marker around the result).
module cmp_mixed #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N+3:0] c,
  output logic         y_lt, y_eq, y_k, y_ge1,
  output logic [N-1:0] y_zext
);
  assign y_lt = a < c;
  assign y_eq = a == c;
  assign y_k = a == 3;
  assign y_ge1 = a >= 1;
  assign y_zext = (a < c);
endmodule
