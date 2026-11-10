`timescale 1ns/1ps
module unsigned_part_negative_range_tb;
  logic [3:-4] w;
  logic [31:0] bu;
  wire [3:0] y;
  unsigned_part_negative_range dut (.*);
  task automatic sample(input logic [31:0] base, input logic [3:0] expected);
    bu = base; #1;
    $display("ROW bu=%h y=%b", bu, y);
    if (y !== expected) $fatal(1, "negative-range select mismatch");
  endtask
  initial begin
    w = 8'b11010110;
    sample(32'hffff_fffe, 4'bxxxx);
    sample(32'hffff_ffff, 4'bxxxx);
    sample(0, 4'b1101);
    $finish;
  end
endmodule
