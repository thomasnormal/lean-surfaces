module divider #(
  parameter int W = 8
) (
  input logic [W-1:0] numerator,
  input logic [W-1:0] denominator,
  output logic [W-1:0] quotient
);
  assign quotient = numerator / denominator;
endmodule
