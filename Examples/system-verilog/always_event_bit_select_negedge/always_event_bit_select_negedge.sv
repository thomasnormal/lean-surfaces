// SPDX-License-Identifier: Apache-2.0
// A constant packed bit-select applies negedge to its sampled bit.
module top;
  logic [3:0] bus = 4'b0100;
  int seen = 0;

  always @(negedge bus[2])
    seen++;

  initial begin
    #1; bus = 4'b0000;
    #1; bus = 4'b0100;
    #1; bus = 4'b0000;
    #1;
    if (seen === 2) $display("ALWAYS EVENT BIT SELECT NEGEDGE PASS");
    else $display("ALWAYS EVENT BIT SELECT NEGEDGE FAIL");
    $finish;
  end
endmodule
