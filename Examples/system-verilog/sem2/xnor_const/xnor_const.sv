// REFUSED (loud; WP-L2): `~^` in a parameter default or a localparam is NOT lowered. The constant
// tier has its own width rules for `~`, and the lowering was measured for signal expressions only, so
// the node stays `BinaryExpression:BinaryXnor` and `load_design_sv2` refuses at the defaults.
module xnor_const #(parameter int N = 4, parameter int Q = (6 ~^ 3)) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  localparam logic [3:0] M = 4'b1010 ~^ 4'b0110;
  assign y = a ^ M[N-1:0];
endmodule
