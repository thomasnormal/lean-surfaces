// SPDX-License-Identifier: Apache-2.0
// A vector bitwise-unary event compares the complete unary result.
module top;
  logic [1:0] bus = 2'b00;
  int seen = 0;
  int baseline;

  always @(~bus)
    seen++;

  initial begin
    #1; baseline = seen;
    bus = 2'b01;
    #1; bus = 2'b11;
    #1;
    if (seen === baseline + 2)
      $display("ALWAYS EVENT VECTOR UNARY PASS");
    else
      $display("ALWAYS EVENT VECTOR UNARY FAIL");
    $finish;
  end
endmodule
