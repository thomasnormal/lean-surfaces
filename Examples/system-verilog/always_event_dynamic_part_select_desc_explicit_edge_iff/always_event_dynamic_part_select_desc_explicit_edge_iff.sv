// SPDX-License-Identifier: Apache-2.0
// Guarded explicit edge on a descending dynamic packed part-select.
module top;
  logic [3:0] bus = 4'b0000;
  logic [2:0] base = 3'd3;
  logic en = 1'b0;
  int seen = 0;

  always @(edge bus[base -: 2] iff en)
    seen++;

  initial begin
    #1; bus = 4'b0100;
    #1; en = 1'b1;
    #1; bus = 4'b1100;
    #1; base = 3'd2;
    #1; bus = 4'b0110;
    #1;
    if (seen === 3) $display("ALWAYS EVENT DYNAMIC DESC EXPLICIT EDGE IFF PASS");
    else $display("ALWAYS EVENT DYNAMIC DESC EXPLICIT EDGE IFF FAIL");
    $finish;
  end
endmodule
