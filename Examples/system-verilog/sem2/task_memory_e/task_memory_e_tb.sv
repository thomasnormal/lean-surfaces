`timescale 1ns/1ps

module task_memory_e_tb;
  logic clk = 1'b0;
  logic [7:0] d = 8'h00;
  wire [7:0] q;

  task_memory_e dut (.*);

  initial begin
    #1;
    $display("ROW before q=%b", q);
    d = 8'ha5; clk = 1'b1; #1;
    $display("ROW edge q=%b", q);
    clk = 1'b0; #1;
    $display("ROW after q=%b", q);
    $finish;
  end
endmodule
