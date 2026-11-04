module remainder (
  input logic [7:0] left,
  input logic [7:0] right,
  output logic [7:0] result
);
  assign result = left % right;
endmodule
