// A fixed packed concatenation is a self-determined constant expression.
module constant_concat #(
  parameter int N = 4
) (
  output logic [7:0] y
);
  localparam logic [7:0] SIGN = {1'b1, 7'b0};
  assign y = SIGN;
endmodule
