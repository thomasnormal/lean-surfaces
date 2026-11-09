// A comparison of two signed operands: the order is two's complement.
module sg_cmp #(parameter integer W = 8) (
  input  logic signed [W-1:0] a, b,
  output logic lt
);
  assign lt = a < b;
endmodule
