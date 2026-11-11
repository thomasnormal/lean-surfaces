`timescale 1ns/1ps

module unpacked_memory_netz_e_tb;
  logic clk = 1'b0;
  logic [7:0] d = 8'h00;
  wire [7:0] q;
  wire zq;

  unpacked_memory_netz_e dut (.*);

  initial begin
    #1;
    $display("ROW before q=%b zq=%b", q, zq);
    d = 8'ha5; clk = 1'b1; #1;
    $display("ROW edge q=%b zq=%b", q, zq);
    clk = 1'b0; #1;
    $display("ROW after q=%b zq=%b", q, zq);
    $finish;
  end
endmodule
