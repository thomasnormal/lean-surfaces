`timescale 1ns/1ps

`ifndef WIDTH
`define WIDTH 4
`endif
`ifndef DEPTH
`define DEPTH 3
`endif
module memory_shape_a_e_tb;
  parameter integer W = `WIDTH;
  parameter integer P = `DEPTH;
  logic clk = 1'b0;
  logic [W-1:0] d = '0;
  logic [P-1:0] idx = '0;
  wire [W-1:0] q;
  wire [W-1:0] selected;

  memory_shape_a_e #(.W(W), .P(P)) dut (.*);

  task automatic row(input integer i);
    $display("ROW W=%0d P=%0d i=%0d q=%b selected=%b", W, P, i, q, selected);
  endtask

  initial begin
    #1; row(0);
    d = {{(W-2){1'b0}}, 2'b10}; idx = '0; clk = 1'b1; #1; row(1);
    d = {{(W-2){1'b0}}, 2'b11}; idx = {{(P-1){1'b0}}, 1'b1}; clk = 1'b0; #1; row(2);
    d = {{(W-3){1'b0}}, 3'b100}; idx = {{(P-1){1'b0}}, 1'b1}; clk = 1'b1; #1; row(3);
    idx = {P{1'bx}}; clk = 1'b0; #1; row(4);
    d = {{(W-3){1'b0}}, 3'b110}; idx = {{(P-2){1'b0}}, 2'b10}; clk = 1'b1; #1; row(5);
    $finish;
  end
endmodule
