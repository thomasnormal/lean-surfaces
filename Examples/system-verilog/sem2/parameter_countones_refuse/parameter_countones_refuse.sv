// Variable-width bit queries remain outside the fixed-width lowering.
module parameter_countones_refuse #(
  parameter int N = 4
) (
  input logic [N-1:0] a,
  output logic [31:0] y
);
  assign y = $countones(a);
endmodule
