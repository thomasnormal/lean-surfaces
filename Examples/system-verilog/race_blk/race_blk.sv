module race_blk (input logic clk);          // blocking assigns: a race
  logic [7:0] a = 8'd1, b = 8'd2;
  always @(posedge clk) a = b;
  always @(posedge clk) b = a;
endmodule
