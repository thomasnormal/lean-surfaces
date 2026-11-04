// SPDX-License-Identifier: Apache-2.0
// Comma-separated explicit edge members use any-change registrations.
module top;
  logic a = 1'b0;
  logic b = 1'b0;
  int seen = 0;

  always @(edge a, edge b)
    seen++;

  initial begin
    #1; a = 1'b1;
    #1; b = 1'b1;
    #1; a = 1'b0;
    #1; b = 1'b0;
    #1;
    if (seen === 4) $display("ALWAYS EVENT EXPLICIT EDGE COMMA PASS");
    else $display("ALWAYS EVENT EXPLICIT EDGE COMMA FAIL");
    $finish;
  end
endmodule
