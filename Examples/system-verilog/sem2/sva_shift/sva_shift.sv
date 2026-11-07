// Clean-room F1 witness for a fixed-width sampled shift expression.
module sva_shift (
  input logic clk,
  input logic [3:0] a,
  output logic [3:0] q
);
  assign q = a << 1;
  assert property (@(posedge clk) (a << 1) == q);
endmodule
