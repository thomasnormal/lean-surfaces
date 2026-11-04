// SPDX-License-Identifier: Apache-2.0
// Explicit edge on a sampled ternary expression uses any result change.
module top;
  logic sel = 1'b0;
  logic [1:0] a = 2'b00;
  logic [1:0] b = 2'b00;
  int seen = 0;

  always @(edge (sel ? a : b))
    seen++;

  initial begin
    #1; b = 2'b01;
    #1; sel = 1'b1;
    #1; a = 2'b10;
    #1; sel = 1'b0;
    #1;
    if (seen === 4) $display("ALWAYS EVENT TERNARY EXPLICIT EDGE PASS");
    else $display("ALWAYS EVENT TERNARY EXPLICIT EDGE FAIL");
    $finish;
  end
endmodule
