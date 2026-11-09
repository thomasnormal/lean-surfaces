`timescale 1ns/1ns
module selects_tb;
  logic clk;
  logic [31:0] d;
  logic [4:0] i;
  logic [7:0] q;
  logic b;
  dark_selects dut(.clk(clk), .d(d), .i(i), .q(q), .b(b));
  task automatic cycle(input logic [31:0] dv, input logic [4:0] iv);
    begin
      d = dv; i = iv; #1; clk = 1; #1;
      $display("ROW q=%b b=%b r=%b", q, b, dut.r);
      clk = 0; #1;
    end
  endtask
  initial begin
    clk = 0; d = 0; i = 0;
    #1;
    $display("ROW q=%b b=%b r=%b", q, b, dut.r);
    cycle(32'hA5A55A5A, 5'd3);
    cycle(32'hA5A55A5A, 5'd3);
    cycle(32'h12345678, 5'd31);
    cycle(32'h12345678, 5'd31);
    $finish;
  end
endmodule
