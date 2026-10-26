/* Discarded time-scale metadata queries have no represented state effect. */
`timescale 1ns/1ps
module top;
  initial begin
    $timeunit;
    $timeprecision;
    $display("PASS");
    $finish;
  end
endmodule
