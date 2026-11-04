// SPDX-License-Identifier: Apache-2.0
// Explicit edge on a dynamic packed bit-select uses any result change.
module top;
  logic [1:0] bus = 2'b00;
  logic idx = 1'b0;
  int seen = 0;

  always @(edge bus[idx])
    seen++;

  initial begin
    #1; bus = 2'b01;
    #1; bus = 2'b00;
    #1; idx = 1'b1;
    #1; bus = 2'b10;
    #1; bus = 2'b00;
    #1;
    if (seen === 4) $display("ALWAYS EVENT DYNAMIC BIT SELECT EXPLICIT EDGE PASS");
    else $display("ALWAYS EVENT DYNAMIC BIT SELECT EXPLICIT EDGE FAIL");
    $finish;
  end
endmodule
