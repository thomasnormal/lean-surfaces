`timescale 1ns/1ps
module memory_shape_d_e_tb;
  localparam integer W = 4;
  logic clk = 1'b0;
  logic [W-1:0] d = '0;
  logic [1:0] idx = 2'b00;
  wire [W-1:0] q;
  wire [W-1:0] selected;

  memory_shape_d_e #(.W(W)) dut (.*);

  task automatic row(input integer i);
    $display("ROW i=%0d q=%b selected=%b", i, q, selected);
  endtask

  initial begin
    #1; row(0);
    d = 4'b0001; idx = 2'b00; clk = 1'b1; #1; row(1);
    d = 4'b0010; idx = 2'b01; clk = 1'b0; #1; row(2);
    d = 4'b0010; idx = 2'b01; clk = 1'b1; #1; row(3);
    d = 4'b0100; idx = 2'b11; clk = 1'b0; #1; row(4);
    d = 4'b0100; idx = 2'b11; clk = 1'b1; #1; row(5);
    idx = 2'bxx; clk = 1'b0; #1; row(6);
    $finish;
  end
endmodule
