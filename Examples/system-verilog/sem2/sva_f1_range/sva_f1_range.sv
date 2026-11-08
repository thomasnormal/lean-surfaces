// Downstream clean-room F1 witness: a finite bounded delay range.
module sva_f1_range(input logic clk, req, ack);
  assert property (@(posedge clk) req |-> ##[1:3] ack);
  cover property (@(posedge clk) req ##[1:3] ack);
endmodule
