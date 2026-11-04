// SPDX-License-Identifier: Apache-2.0
// A multibit packed identifier applies negedge to its sampled result LSB.
module top;
  logic [3:0] bus = 4'b0011;
  int seen = 0;

  always @(negedge bus)
    seen++;

  initial begin
    #1; bus = 4'b0010;
    #1; bus = 4'b0000;
    #1; bus = 4'b0001;
    #1; bus = 4'b0000;
    #1;
    if (seen === 2) $display("ALWAYS EVENT MULTIBIT NEGEDGE PASS");
    else $display("ALWAYS EVENT MULTIBIT NEGEDGE FAIL");
    $finish;
  end
endmodule
