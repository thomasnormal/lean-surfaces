// A signed comparison of two signals declared with different packed dimensions: at W = 8 the widths agree, at any
// other W the narrower operand would be sign-extended (IEEE 1800-2023 §11.8.2).
module sg_cmp_dims #(parameter integer W = 8) (
  input  logic signed [W-1:0] a,
  input  logic signed [7:0] b,
  output logic y
);
  assign y = a < b;
endmodule
