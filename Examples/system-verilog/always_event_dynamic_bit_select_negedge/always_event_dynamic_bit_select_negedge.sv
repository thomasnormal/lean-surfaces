// SPDX-License-Identifier: Apache-2.0
// A dynamic packed bit-select applies the edge rule to its sampled bit.
module top;
  logic [1:0] bus = 2'b11;
  logic idx = 1'b0;
  int seen = 0;

  always @(negedge bus[idx])
    seen++;

  initial begin
    #1; bus = 2'b10;
    #1; bus = 2'b11;
    #1; idx = 1'b1;
    #1; bus = 2'b01;
    #1;
    if (seen === 2) $display("ALWAYS EVENT DYNAMIC BIT SELECT NEGEDGE PASS");
    else $display("ALWAYS EVENT DYNAMIC BIT SELECT NEGEDGE FAIL");
    $finish;
  end
endmodule
