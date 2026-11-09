// A signed operand added into a wider signed target: each operand is sign-extended first.
module sg_ext #(parameter integer W = 8) (
  input  logic signed [W-1:0] a, b,
  output logic signed [W:0]   s
);
  assign s = a + b;
endmodule
