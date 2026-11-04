// SPDX-License-Identifier: Apache-2.0
// A scalar-condition ternary event compares its complete packed result.
module top;
  logic sel = 1'b0;
  logic [1:0] a = 2'b00;
  logic [1:0] b = 2'b01;
  int seen = 0;
  int baseline;

  always @(sel ? a : b)
    seen++;

  initial begin
    #1; baseline = seen;
    b = 2'b10;
    #1; a = 2'b11;
    #1; sel = 1'b1;
    #1; b = 2'b00;
    #1; a = 2'b00;
    #1;
    if (seen === baseline + 3)
      $display("ALWAYS EVENT VECTOR TERNARY PASS");
    else
      $display("ALWAYS EVENT VECTOR TERNARY FAIL");
    $finish;
  end
endmodule
