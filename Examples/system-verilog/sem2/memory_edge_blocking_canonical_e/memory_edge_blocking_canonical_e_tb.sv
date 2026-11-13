`timescale 1ns/1ps

module memory_edge_blocking_canonical_e_tb;
  logic clk = 1'b0;
  logic [3:0] d = 4'd3;
  wire [3:0] mem0;
  wire [3:0] mem1;
  wire [3:0] delayed;
  wire [3:0] marker;

  memory_edge_blocking_canonical_e #(.W(4)) dut (.*);

  initial begin
    #1 $display("ROW i=0 mem0=%b mem1=%b delayed=%b marker=%b", mem0, mem1, delayed, marker);
    d = 4'd10; clk = 1'b1; #1;
    $display("ROW i=1 mem0=%b mem1=%b delayed=%b marker=%b", mem0, mem1, delayed, marker);
    clk = 1'b0; d = 4'd11; #1;
    clk = 1'b1; #1;
    $display("ROW i=2 mem0=%b mem1=%b delayed=%b marker=%b", mem0, mem1, delayed, marker);
    $finish;
  end
endmodule
