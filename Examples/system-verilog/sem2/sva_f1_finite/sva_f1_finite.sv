// Downstream clean-room F1 witness: finite implication, disable iff,
// $rose and finite $past in a retained assert/assume pair.
module sva_f1_finite(input logic clk, rst, req, ack, output logic q);
  always_ff @(posedge clk or negedge rst)
    if (!rst) q <= 1'b0; else q <= req;
  assert property (@(posedge clk) disable iff (rst) req |-> ##1 ack);
  assume property (@(posedge clk) $rose(req) |=> $past(ack, 1));
endmodule
