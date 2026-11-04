// SPDX-License-Identifier: Apache-2.0
// A packed bitwise-binary event compares the complete result vector.
module top;
  logic [1:0] a = 2'b00;
  logic [1:0] b = 2'b01;
  int seen = 0;
  int baseline;

  always @(a | b)
    seen++;

  initial begin
    #1; baseline = seen;
    a = 2'b10;
    #1; b = 2'b11;
    #1; a = 2'b00;
    #1; b = 2'b00;
    #1;
    if (seen === baseline + 2)
      $display("ALWAYS EVENT VECTOR BINARY PASS");
    else
      $display("ALWAYS EVENT VECTOR BINARY FAIL");
    $finish;
  end
endmodule
