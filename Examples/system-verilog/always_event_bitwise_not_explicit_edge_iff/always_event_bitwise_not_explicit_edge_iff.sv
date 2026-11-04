// SPDX-License-Identifier: Apache-2.0
// Explicit edge and iff guard apply to a sampled bitwise-not result.
module top;
  logic [1:0] bus = 2'b00;
  logic en = 1'b0;
  int seen = 0;

  always @(edge ~bus iff en)
    seen++;

  initial begin
    #1; bus = 2'b01;
    #1; en = 1'b1;
    #1; bus = 2'b11;
    #1; bus = 2'b10;
    #1;
    if (seen === 2) $display("ALWAYS EVENT BITWISE NOT EXPLICIT EDGE IFF PASS");
    else $display("ALWAYS EVENT BITWISE NOT EXPLICIT EDGE IFF FAIL");
    $finish;
  end
endmodule
