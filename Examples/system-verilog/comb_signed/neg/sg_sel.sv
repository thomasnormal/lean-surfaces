// The sign bit of a signed operand, read by a bit select.
module sg_sel #(parameter integer W = 8) (
  input  logic signed [W-1:0] a,
  output logic neg
);
  assign neg = a[W-1];
endmodule
