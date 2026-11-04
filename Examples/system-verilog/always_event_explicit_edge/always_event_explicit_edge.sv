// SPDX-License-Identifier: Apache-2.0
// Plain always @(edge ...) uses the retained any-change registration.
module top;
  logic [1:0] bus = 2'b00;
  int seen = 0;

  always @(edge bus)
    seen++;

  initial begin
    #1; bus = 2'b01;
    #1; bus = 2'b11;
    #1; bus = 2'b10;
    #1; bus = 2'b00;
    #1;
    if (seen === 4) $display("ALWAYS EVENT EXPLICIT EDGE PASS");
    else $display("ALWAYS EVENT EXPLICIT EDGE FAIL");
    $finish;
  end
endmodule
