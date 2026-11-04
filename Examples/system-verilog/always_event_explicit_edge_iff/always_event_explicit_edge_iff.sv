// SPDX-License-Identifier: Apache-2.0
// Explicit edge and iff guard share the retained event registration.
module top;
  logic a = 1'b0;
  logic en = 1'b0;
  int seen = 0;

  always @(edge a iff en)
    seen++;

  initial begin
    #1; a = 1'b1;
    #1; en = 1'b1;
    #1; a = 1'b0;
    #1; a = 1'b1;
    #1;
    if (seen === 2) $display("ALWAYS EVENT EXPLICIT EDGE IFF PASS");
    else $display("ALWAYS EVENT EXPLICIT EDGE IFF FAIL");
    $finish;
  end
endmodule
