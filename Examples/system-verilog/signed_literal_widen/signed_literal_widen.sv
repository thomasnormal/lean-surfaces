// Clean-room regression for IEEE 1800-2023 §§11.8.1 and 11.8.2:
// a sized signed literal is sign-extended when both operands are signed,
// but is zero-extended in a mixed signed/unsigned expression.
module signed_literal_widen #(parameter int W = 8) (
  input  logic signed [W-1:0] x,
  input  logic        [W-1:0] u,
  output logic signed [W-1:0] y,
  output logic        [W-1:0] mixed,
  output logic ge
);
  assign y = x + 8'sb1000_0000;
  assign mixed = u + 8'sb1000_0000;
  assign ge = x >= 8'sb1000_0000;
endmodule
