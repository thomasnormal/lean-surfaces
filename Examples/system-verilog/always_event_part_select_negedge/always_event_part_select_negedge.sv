// SPDX-License-Identifier: Apache-2.0
// A constant packed part-select applies negedge to its sampled result LSB.
module top;
  logic [3:0] bus = 4'b0011;
  int seen = 0;

  always @(negedge bus[3:0])
    seen++;

  initial begin
    #1; bus = 4'b1011;
    #1; bus = 4'b1010;
    #1; bus = 4'b1000;
    #1; bus = 4'b1001;
    #1; bus = 4'b1000;
    #1;
    if (seen === 2) $display("ALWAYS EVENT PART SELECT NEGEDGE PASS");
    else $display("ALWAYS EVENT PART SELECT NEGEDGE FAIL");
    $finish;
  end
endmodule
