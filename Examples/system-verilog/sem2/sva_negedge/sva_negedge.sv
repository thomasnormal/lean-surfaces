// Clean-room F1 witness: a finite non-overlapped implication sampled on negedge.
module sva_negedge(input logic clk, req, ack);
  assert property (@(negedge clk) req |=> ack);
  cover property (@(negedge clk) req ##1 ack);
endmodule
