// SPDX-License-Identifier: Apache-2.0
// Explicit edge and iff guard apply to a sampled binary expression.
module top;
  logic [1:0] a = 2'b00;
  logic [1:0] b = 2'b00;
  logic en = 1'b0;
  int seen = 0;

  always @(edge (a | b) iff en)
    seen++;

  initial begin
    #1; a = 2'b01;
    #1; en = 1'b1;
    #1; b = 2'b10;
    #1; a = 2'b00;
    #1;
    if (seen === 2) $display("ALWAYS EVENT BINARY EXPLICIT EDGE IFF PASS");
    else $display("ALWAYS EVENT BINARY EXPLICIT EDGE IFF FAIL");
    $finish;
  end
endmodule
