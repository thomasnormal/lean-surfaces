// The arithmetic shift right `>>>` of a signed operand (IEEE 1800-2023 §11.4.10): the vacated bits take the sign bit,
// and the amount is read as unsigned. A left shift of a signed operand fills with zeros, as for an unsigned one. Every
// target is as wide as the shifted operand.
module asr #(parameter integer W = 8) (
  input  logic signed [W-1:0] a,
  input  logic        [2:0]   s,
  output logic signed [W-1:0] y, z,
  output logic        [W-1:0] l
);
  assign y = a >>> s;
  assign z = a >>> 1;
  assign l = a << s;
endmodule
