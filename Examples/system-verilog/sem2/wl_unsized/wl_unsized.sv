// WP-B2 pin P5: an unsized constant is a 32-bit operand: `a + 1` is computed at 32 bits and truncated, `a == 3` and `a < 1` compare at 32 bits.
module wl_unsized (
  input  logic [3:0] a,
  output logic [3:0] y_inc,
  output logic [4:0] y_inc5,
  output logic y_eq,
  output logic y_lt
);
  assign y_inc = a + 1;
  assign y_inc5 = a + 1;
  assign y_eq = (a == 3);
  assign y_lt = (a < 1);
endmodule
