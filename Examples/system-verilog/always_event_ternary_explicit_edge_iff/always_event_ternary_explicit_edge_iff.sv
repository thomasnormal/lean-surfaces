// SPDX-License-Identifier: Apache-2.0
// Explicit edge and iff guard apply to a sampled ternary expression.
module top;
  logic sel = 1'b0;
  logic [1:0] a = 2'b00;
  logic [1:0] b = 2'b00;
  logic en = 1'b0;
  int seen = 0;

  always @(edge (sel ? a : b) iff en)
    seen++;

  initial begin
    #1; b = 2'b01;
    #1; en = 1'b1;
    #1; sel = 1'b1;
    #1; a = 2'b10;
    #1;
    if (seen === 2) $display("ALWAYS EVENT TERNARY EXPLICIT EDGE IFF PASS");
    else $display("ALWAYS EVENT TERNARY EXPLICIT EDGE IFF FAIL");
    $finish;
  end
endmodule
