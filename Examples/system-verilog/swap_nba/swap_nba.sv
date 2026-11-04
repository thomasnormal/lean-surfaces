module swap_nba (input logic clk);          // nonblocking: correct swap
  logic [7:0] a = 8'd1, b = 8'd2;
  always @(posedge clk) a <= b;
  always @(posedge clk) b <= a;
endmodule
