// Clean-room F1 witness for four-state $onehot0.
module sva_onehot0 (
  input logic clk,
  input logic [3:0] a,
  output logic q
);
  assign q = $onehot0(a);
  assert property (@(posedge clk) $onehot0(a));
endmodule
