// WP-B2 pin P2: a comparison is self-determined with a one-bit result (zero-extended into a wider target), its operands are extended to the larger operand width; `==` is 0 on a known mismatch even with x elsewhere, `<` is x when an operand has an x.
module wl_cmp_ctx (
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic [7:0] c,
  output logic [3:0] y_zext,
  output logic [3:0] y_and,
  output logic y_lt48,
  output logic y_eq48,
  output logic [4:0] y_cat
);
  assign y_zext = (a < b);
  assign y_and = a & (a == b);
  assign y_lt48 = (b < c);
  assign y_eq48 = (a == c);
  assign y_cat = {a < b, a};
endmodule
