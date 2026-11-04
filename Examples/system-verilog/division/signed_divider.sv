module signed_divider #(
  parameter int W = 8
) (
  input logic signed [W-1:0] numerator,
  input logic signed [W-1:0] denominator,
  output logic signed [W-1:0] quotient
);
  assign quotient = numerator / denominator;
endmodule
