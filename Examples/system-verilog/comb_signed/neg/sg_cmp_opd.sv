// A signed comparison whose left operand is an expression, not a whole signed signal.
module sg_cmp_opd #(parameter integer W = 8) (
  input  logic signed [W-1:0] a, b, c,
  output logic y
);
  assign y = (a + b) < c;
endmodule
