`timescale 1ns/1ps

module unpacked_cpuregs_canonical_e_tb;
  logic clk = 1'b0;
  logic [4:0] raddr = 5'd0;
  logic [4:0] waddr = 5'd3;
  logic [31:0] wdata = 32'h000000a5;
  logic we = 1'b0;
  wire [31:0] rdata;

  unpacked_cpuregs_canonical_e dut (.*);

  initial begin
    #1;
    $display("ROW before rdata=%b", rdata);
    we = 1'b1; clk = 1'b1; #1;
    $display("ROW write3 rdata=%b", rdata);
    clk = 1'b0; we = 1'b0; raddr = 5'd3; #1;
    $display("ROW read3 rdata=%b", rdata);
    raddr = 5'bxxxxx; #1;
    $display("ROW xread rdata=%b", rdata);
    raddr = 5'bzzzzz; #1;
    $display("ROW zread rdata=%b", rdata);
    raddr = 5'd3; waddr = 5'bxxxxx; wdata = 32'h0000005a;
    we = 1'b1; clk = 1'b1; #1;
    $display("ROW xwrite rdata=%b", rdata);
    clk = 1'b0; we = 1'b0; raddr = 5'd3; #1;
    $display("ROW afterxwrite rdata=%b", rdata);
    waddr = 5'd7; wdata = 32'h0000005a; we = 1'b1; clk = 1'b1; #1;
    $display("ROW write7 rdata=%b", rdata);
    clk = 1'b0; we = 1'bx; raddr = 5'd7; #1;
    $display("ROW xwe_noedge rdata=%b", rdata);
    clk = 1'b1; #1;
    $display("ROW xwe_edge rdata=%b", rdata);
    clk = 1'b0; we = 1'b0; raddr = 5'd7; #1;
    $display("ROW afterxwe rdata=%b", rdata);
    $finish;
  end
endmodule
