`timescale 1ns/1ps
module unsigned_part_base_tb;
  logic [7:0] v;
  logic [3:0] s;
  logic [31:0] bu;
  wire [3:0] by_sub, by_base;
  unsigned_part_base dut (.*);
  task automatic sample(input logic [3:0] si, input logic [31:0] bi,
                        input logic [3:0] expected);
    s = si; bu = bi; #1;
    $display("ROW s=%b bu=%h sub=%b base=%b", s, bu, by_sub, by_base);
    if (by_sub !== expected || by_base !== expected) $fatal(1, "unsigned part-select mismatch");
  endtask
  initial begin
    v = 8'hd6;
    sample(0, 32'hffff_fffe, 4'bxxxx);
    sample(1, 32'hffff_ffff, 4'bxxxx);
    sample(2, 0, 4'b0110);
    sample(3, 1, 4'b1011);
    sample(6, 4, 4'b1101);
    sample(4'bx000, 32'b000000000000000000000000000000x0, 4'bxxxx);
    sample(4'bz000, 32'b000000000000000000000000000000z0, 4'bxxxx);
    $finish;
  end
endmodule
