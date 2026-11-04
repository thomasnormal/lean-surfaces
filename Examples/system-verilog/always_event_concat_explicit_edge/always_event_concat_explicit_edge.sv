// SPDX-License-Identifier: Apache-2.0
// Explicit edge on a sampled concatenation uses any result change.
module top;
  logic a = 1'b0;
  logic b = 1'b0;
  int seen = 0;

  always @(edge {a, b})
    seen++;

  initial begin
    #1; a = 1'b1;
    #1; b = 1'b1;
    #1; a = 1'b0;
    #1; b = 1'b0;
    #1;
    if (seen === 4) $display("ALWAYS EVENT CONCAT EXPLICIT EDGE PASS");
    else $display("ALWAYS EVENT CONCAT EXPLICIT EDGE FAIL");
    $finish;
  end
endmodule
