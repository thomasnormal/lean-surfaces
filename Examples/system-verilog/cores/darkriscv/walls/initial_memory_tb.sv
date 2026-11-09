`timescale 1ns/1ns
module initial_memory_tb;
  logic clk = 1'b0;
  logic [7:0] q;
  initial_memory #(.W(8)) dut (.clk(clk), .q(q));
  initial begin
    #1 $display("ROW q=%h", q);
    #1 $finish;
  end
endmodule
