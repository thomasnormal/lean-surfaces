`timescale 1ns/1ps
module memory_edge_incdec_e_tb;
  logic clk = 1'b0;
  logic rstn = 1'b1;
  logic [7:0] d = 8'h00;
  wire [7:0] q;
  memory_edge_incdec_e #(.W(8), .N(4)) dut (.*);
  initial begin
    #1;
    rstn = 1'b0; d = 8'h03; clk = 1'b1; #1;
    $display("ROW 0 q=%b", q);
    clk = 1'b0; rstn = 1'b1; d = 8'h11; #1;
    $display("ROW 1 q=%b", q);
    clk = 1'b1; #1;
    $display("ROW 2 q=%b", q);
    clk = 1'b0; d = 8'h22; #1;
    $display("ROW 3 q=%b", q);
    clk = 1'b1; #1;
    $display("ROW 4 q=%b", q);
    $finish;
  end
endmodule
