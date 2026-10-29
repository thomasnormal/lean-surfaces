/*
:name: pure_scalar_metadata_statements_adapter
:description: Discarded scalar metadata queries carry no adapter state.
:tags: 6.11,20.4,20.6
:type: simulation
*/
`timescale 1ns/1ps
module top;
  int counter;
  initial begin
    $clog2(8);
    $isunbounded(5);
    $signed(8'hff);
    $unsigned(counter);
    $timeunit;
    $timeprecision;
    $display("PASS");
    $finish;
  end
endmodule
