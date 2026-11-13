`timescale 1ns/1ps

module memory_edge_case_canonical_e_tb;
  logic clk = 1'b0;
  logic [1:0] sel = 2'd0;
  logic [3:0] d = 4'd3;
  wire [3:0] q0;
  wire [3:0] q1;
  wire [3:0] hit;

  memory_edge_case_canonical_e #(.W(4)) dut (.*);

  initial begin
    #1 $display("ROW i=0 q0=%b q1=%b hit=%b", q0, q1, hit);
    d = 4'd10; clk = 1'b1; #1;
    $display("ROW i=1 q0=%b q1=%b hit=%b", q0, q1, hit);
    clk = 1'b0; sel = 2'd1; d = 4'd11; #1;
    $display("ROW i=2 q0=%b q1=%b hit=%b", q0, q1, hit);
    clk = 1'b1; #1;
    $display("ROW i=3 q0=%b q1=%b hit=%b", q0, q1, hit);
    clk = 1'b0; sel = 2'd2; d = 4'd12; #1;
    $display("ROW i=4 q0=%b q1=%b hit=%b", q0, q1, hit);
    clk = 1'b1; #1;
    $display("ROW i=5 q0=%b q1=%b hit=%b", q0, q1, hit);
    $finish;
  end
endmodule
