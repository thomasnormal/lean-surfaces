module sva_inside_e(input logic clk, input logic [3:0] a);
  ap: assert property (@(posedge clk) a inside {4'b0001});
endmodule
