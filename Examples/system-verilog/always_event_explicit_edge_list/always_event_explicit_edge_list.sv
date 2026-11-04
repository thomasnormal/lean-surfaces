// SPDX-License-Identifier: Apache-2.0
// Explicit edge members in an event list use any-change registrations.
module top;
  logic a = 1'b0;
  logic b = 1'b0;
  int seen = 0;

  always @(edge a or edge b)
    seen++;

  initial begin
    #1; a = 1'b1;
    #1; b = 1'b1;
    #1; a = 1'b0;
    #1; b = 1'b0;
    #1;
    if (seen === 4) $display("ALWAYS EVENT EXPLICIT EDGE LIST PASS");
    else $display("ALWAYS EVENT EXPLICIT EDGE LIST FAIL");
    $finish;
  end
endmodule
