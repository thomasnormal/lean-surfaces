// SPDX-License-Identifier: Apache-2.0
// Comma-separated explicit edge members retain individual iff guards.
module top;
  logic a = 1'b0;
  logic b = 1'b0;
  logic en = 1'b0;
  int seen = 0;

  always @(edge a iff en, edge b iff en)
    seen++;

  initial begin
    #1; a = 1'b1;
    #1; en = 1'b1;
    #1; b = 1'b1;
    #1; a = 1'b0;
    #1; b = 1'b0;
    #1;
    if (seen === 3) $display("ALWAYS EVENT EXPLICIT EDGE COMMA IFF PASS");
    else $display("ALWAYS EVENT EXPLICIT EDGE COMMA IFF FAIL");
    $finish;
  end
endmodule
