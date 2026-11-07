// Clean-room F1 witness for `$past` inside a sampled value expression.
module sva_past_value (
  input logic clk,
  input logic valid,
  input logic inc,
  input logic [3:0] depth,
  output logic q
);
  assign q = depth[0];
  assert property (@(posedge clk) (valid && !inc) |=> depth == $past(depth));
  assert property (@(posedge clk) (valid && inc) |=> depth == $past(depth) + 1);
endmodule
