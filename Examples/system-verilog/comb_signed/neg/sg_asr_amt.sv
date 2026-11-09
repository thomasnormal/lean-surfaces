// An arithmetic shift right whose amount is a signed signal (IEEE 1800-2023 §11.4.10 reads it as unsigned).
module sg_asr_amt #(parameter integer W = 8) (
  input  logic signed [W-1:0] a,
  input  logic signed [2:0]   b,
  output logic signed [W-1:0] y
);
  assign y = a >>> b;
endmodule
