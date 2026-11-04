// WP-B2 gate 2b pin P11: comparisons of operands of different widths (the narrower is zero-extended), against an unsized constant (32 bits wide) and into a wider target (the one-bit result is zero-extended).
module wl_cmp_mixed (
  input  logic [3:0] a,
  input  logic [7:0] c,
  output logic y_lt,
  output logic y_eq,
  output logic y_k,
  output logic y_ge1,
  output logic [3:0] y_zext
);
  assign y_lt = a < c;
  assign y_eq = a == c;
  assign y_k = a == 3;
  assign y_ge1 = a >= 1;
  assign y_zext = (a < c);
endmodule
