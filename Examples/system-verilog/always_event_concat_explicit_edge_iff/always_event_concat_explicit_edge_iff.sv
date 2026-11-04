// SPDX-License-Identifier: Apache-2.0
// Explicit edge and iff guard apply to a sampled concatenation.
module top;
  logic a = 1'b0;
  logic b = 1'b0;
  logic en = 1'b0;
  int seen = 0;

  always @(edge {a, b} iff en)
    seen++;

  initial begin
    #1; a = 1'b1;
    #1; en = 1'b1;
    #1; b = 1'b1;
    #1; a = 1'b0;
    #1;
    if (seen === 2) $display("ALWAYS EVENT CONCAT EXPLICIT EDGE IFF PASS");
    else $display("ALWAYS EVENT CONCAT EXPLICIT EDGE IFF FAIL");
    $finish;
  end
endmodule
