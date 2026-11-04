// SPDX-License-Identifier: Apache-2.0
// A scalar binary event compares the evaluated result, not operand changes.
module top;
  logic a = 1'b0;
  logic b = 1'b0;
  logic d = 1'b0;
  logic q = 1'b1;

  always @(a | b)
    q = d;

  initial begin
    #1; a = 1'b1;
    #1; b = 1'b1;
    #1; a = 1'b0;
    #1; b = 1'b0;
    #1;
    if (q === 1'b0) $display("ALWAYS EVENT BINARY PASS");
    else $display("ALWAYS EVENT BINARY FAIL");
    $finish;
  end
endmodule
