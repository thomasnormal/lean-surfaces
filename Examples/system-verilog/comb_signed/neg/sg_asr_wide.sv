// An arithmetic shift right into a target one bit wider than the operand: the operand is sign-extended before the
// shift (IEEE 1800-2023 §11.6.1, §11.8.2).
module sg_asr_wide #(parameter integer W = 8) (
  input  logic signed [W-1:0] a,
  input  logic        [2:0]   s,
  output logic signed [W:0]   y
);
  assign y = a >>> s;
endmodule
