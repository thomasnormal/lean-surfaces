// A signed comparison as an operand of `&&`: a self-determined position (IEEE 1800-2023 §11.6.1).
module sg_cmp_self #(parameter integer W = 8) (
  input  logic signed [W-1:0] a, b,
  input  logic en,
  output logic y
);
  assign y = en && (a < b);
endmodule
