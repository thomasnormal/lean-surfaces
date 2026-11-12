`timescale 1ns/1ps
module param_mem_shift_e_tb;
 logic clk=0; logic [7:0] d=0; wire [7:0] q;
 param_mem_shift_e #(.W(8),.P(4)) dut(.*);
 initial begin
  #1 $display("ROW 0 q=%b",q); d=8'ha5; clk=1; #1 $display("ROW 1 q=%b",q);
  clk=0; d=8'h5a; #1 $display("ROW 2 q=%b",q); clk=1; #1 $display("ROW 3 q=%b",q);
  clk=0; d=8'hxx; #1 $display("ROW 4 q=%b",q); $finish;
 end
endmodule
