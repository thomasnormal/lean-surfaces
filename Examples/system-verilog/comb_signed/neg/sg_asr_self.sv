// An arithmetic shift right as an operand of `&&`: a self-determined position (IEEE 1800-2023 §11.6.1).
module sg_asr_self #(parameter integer W = 8) (
  input  logic signed [W-1:0] a,
  input  logic en,
  output logic y
);
  assign y = en && (a >>> 1);
endmodule
