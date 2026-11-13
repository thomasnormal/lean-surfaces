`timescale 1ns/1ps

module memory_edge_casez_casex_canonical_e_tb;
  logic clk = 1'b0;
  logic [3:0] sel = 4'bxxxx;
  logic [3:0] d = 4'bxxxx;
  wire [3:0] qz;
  wire [3:0] qx;
  wire [3:0] plain;

  memory_edge_casez_casex_canonical_e #(.W(4), .D(2)) dut (.*);

  always #5 clk = ~clk;

  task automatic row(input logic [8*24-1:0] name,
                     input logic [3:0] s,
                     input logic [3:0] value);
    begin
      @(negedge clk);
      sel = s;
      d = value;
      @(posedge clk);
      #1 $display("ROW %0s qz=%b qx=%b plain=%b", name, qz, qx, plain);
    end
  endtask

  initial begin
    #1 $display("ROW first qz=%b qx=%b plain=%b", qz, qx, plain);
    row("sel_0000_d9", 4'b0000, 4'b1001);
    row("sel_0001_d8", 4'b0001, 4'b1000);
    row("sel_01xz_d7", 4'b01xz, 4'b0111);
    row("sel_1x00_d6", 4'b1x00, 4'b0110);
    row("sel_zzzz_d5", 4'bzzzz, 4'b0101);
    $finish;
  end
endmodule
