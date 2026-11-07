// Downstream clean-room F1 witness: an assume with disable iff and $stable.
module sva_assume_disable(input logic clk, rst, valid, data);
  assume property (@(posedge clk) disable iff (!rst) valid |-> $stable(data));
endmodule
