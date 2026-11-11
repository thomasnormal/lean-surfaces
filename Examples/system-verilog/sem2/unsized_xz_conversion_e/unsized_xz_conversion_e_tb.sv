`timescale 1ns/1ps
module unsized_xz_conversion_e_tb;
  logic clk;
  wire [39:0] qx40, qz40, qhx40, qhz40, mem40;
  wire [7:0] qx8, qz8, qhx8, qhz8, mem8;

  unsized_xz_conversion_e #(.N(40)) d40
    (.clk(clk), .qx(qx40), .qz(qz40), .qhx(qhx40), .qhz(qhz40), .mem_q(mem40));
  unsized_xz_conversion_e #(.N(8)) d8
    (.clk(clk), .qx(qx8), .qz(qz8), .qhx(qhx8), .qhz(qhz8), .mem_q(mem8));

  task automatic row(input [8*6-1:0] name);
    begin
      #1 $display("ROW %0s qx40=%b qz40=%b qhx40=%b qhz40=%b qx8=%b qz8=%b qhx8=%b qhz8=%b mem40=%b mem8=%b",
                  name, qx40, qz40, qhx40, qhz40, qx8, qz8, qhx8, qhz8,
                  mem40, mem8);
    end
  endtask

  initial begin
    clk = 1'b0;
    row("before");
    #1 clk = 1'b1;
    row("edge");
    $finish;
  end
endmodule
