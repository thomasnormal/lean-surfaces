// An arithmetic shift right of a signed operand: the sign bit is replicated.
module sg_asr #(parameter integer W = 8) (
  input  logic signed [W-1:0] a,
  output logic signed [W-1:0] y
);
  assign y = a >>> 1;
endmodule
