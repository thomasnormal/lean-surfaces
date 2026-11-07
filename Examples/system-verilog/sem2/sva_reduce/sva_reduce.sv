// Clean-room F1 witness for a reduction expression in an SVA property.
module sva_reduce (
  input logic clk,
  input logic [3:0] a,
  output logic q
);
  assign q = |a;
  assert property (@(posedge clk) (|a) == q);
endmodule
