// Two's-complement arithmetic on signed operands of one width W: the sum, the difference, a bitwise mix, and a
// signed input copied to an unsigned output. Every operand is exactly as wide as its target, so no operand is
// extended, and a signed read means the same bits as the unsigned read of the same signal.
module sadd #(parameter integer W = 8) (
  input  logic signed [W-1:0] a, b,
  output logic signed [W-1:0] s, d,
  output logic        [W-1:0] x, y
);
  assign s = a + b;
  assign d = a - b;
  assign x = a ^ ~b;
  assign y = a;
endmodule
