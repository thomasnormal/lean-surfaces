// The Verilog-2001 spelling of `pi_nonansi`: a `reg` with an initializer.
module pi_nonansi_reg(clk, a, y);
  input clk;
  input a;
  output [1:0] y;
  reg [1:0] y = 2'b10;
  always @(posedge clk) y[0] <= a;
endmodule
