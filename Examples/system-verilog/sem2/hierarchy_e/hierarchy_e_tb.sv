`timescale 1ns/1ps
module hierarchy_e_tb;
  logic [7:0] a;
  wire [7:0] y;
  hierarchy_parameterized #(.W(8)) dut (.a(a), .y(y));
  initial begin
    a = 8'b00000000; #1; $display("ROW 0 y=%b", y);
    a = 8'b00000001; #1; $display("ROW 1 y=%b", y);
    a = 8'b10100101; #1; $display("ROW 2 y=%b", y);
    a = 8'b11110000; #1; $display("ROW 3 y=%b", y);
    a = 8'bxxxxxxxx; #1; $display("ROW 4 y=%b", y);
    $finish;
  end
endmodule
