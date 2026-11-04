module signed_remainder #(
  parameter int W = 8
) (
  input logic signed [W-1:0] left,
  input logic signed [W-1:0] right,
  output logic signed [W-1:0] result
);
  assign result = left % right;
endmodule
