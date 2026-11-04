// SPDX-License-Identifier: Apache-2.0
// Explicit edge on a sampled binary expression uses any result change.
module top;
  logic [1:0] a = 2'b00;
  logic [1:0] b = 2'b00;
  int seen = 0;

  always @(edge (a | b))
    seen++;

  initial begin
    #1; a = 2'b01;
    #1; a = 2'b00;
    #1; b = 2'b10;
    #1; b = 2'b00;
    #1;
    if (seen === 4) $display("ALWAYS EVENT BINARY EXPLICIT EDGE PASS");
    else $display("ALWAYS EVENT BINARY EXPLICIT EDGE FAIL");
    $finish;
  end
endmodule
