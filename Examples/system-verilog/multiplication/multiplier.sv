module multiplier #(
  parameter int W = 8
) (
  input logic [W-1:0] left,
  input logic [W-1:0] right,
  output logic [W-1:0] product
);
  assign product = left * right;
endmodule
