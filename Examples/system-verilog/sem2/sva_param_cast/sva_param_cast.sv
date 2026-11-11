// Clean-room F1 witness for a parameter-sized sampled cast.
module sva_param_cast #(
  parameter int N = 4
) (
  input logic clk,
  input logic [N-1:0] a,
  output logic [N-1:0] q
);
  assign q = a;
  assert property (@(posedge clk) a |-> a > (N'(1) << $past(a)));
endmodule
