// SPDX-License-Identifier: Apache-2.0
// Explicit edge and iff guard apply to a dynamic packed bit-select.
module top;
  logic [1:0] bus = 2'b00;
  logic idx = 1'b0;
  logic en = 1'b0;
  int seen = 0;

  always @(edge bus[idx] iff en)
    seen++;

  initial begin
    #1; bus = 2'b01;
    #1; en = 1'b1;
    #1; bus = 2'b00;
    #1; idx = 1'b1;
    #1; bus = 2'b10;
    #1;
    if (seen === 2) $display("ALWAYS EVENT DYNAMIC BIT SELECT EXPLICIT EDGE IFF PASS");
    else $display("ALWAYS EVENT DYNAMIC BIT SELECT EXPLICIT EDGE IFF FAIL");
    $finish;
  end
endmodule
