module signed_m0(
  input logic signed [7:0] a,
  input logic signed [7:0] b,
  output logic signed [7:0] sum,
  output logic lt);
  assign sum = a + b;
  assign lt = a < b;
endmodule
