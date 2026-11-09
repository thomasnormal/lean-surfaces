`timescale 1ns/1ns
module unsized_xz_memory_tb;
  logic clk;
  logic [63:0] qx, qz, qhx, qhz;
  logic [7:0] qm;
  unsized_xz_memory #(.N(8)) dut
    (.clk(clk), .qx(qx), .qz(qz), .qhx(qhx), .qhz(qhz), .qm(qm));

  initial begin
    clk = 0;
    #1;
    $display("ROW qx=%b qz=%b qhx=%b qhz=%b qm=%b", qx, qz, qhx, qhz, qm);
    clk = 1;
    #1;
    $display("ROW qx=%b qz=%b qhx=%b qhz=%b qm=%b", qx, qz, qhx, qhz, qm);
    $finish;
  end
endmodule
