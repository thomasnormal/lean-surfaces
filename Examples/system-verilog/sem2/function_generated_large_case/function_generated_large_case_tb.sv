`timescale 1ns/1ps

module function_generated_large_case_tb;
  logic [64:0] a;
  wire [64:0] y;
  function_generated_large_case dut(.a(a), .y(y));

  task automatic row(input [8*8-1:0] name, input logic [64:0] value);
    begin
      a = value;
      #1 $display("ROW %0s a=%b y=%b", name, a, y);
    end
  endtask

  initial begin
    row("zero", 65'b0);
    row("one", 65'b1);
    row("ones", {65{1'b1}});
    $finish;
  end
endmodule
