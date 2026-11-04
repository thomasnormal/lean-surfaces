// SPDX-License-Identifier: Apache-2.0
// A unary event compares the evaluated scalar result.
module top;
  logic a = 1'b0;
  logic d = 1'b0;
  logic q = 1'b1;

  always @(~a)
    q = d;

  initial begin
    #1; a = 1'b1;
    #1;
    if (q === 1'b0) $display("ALWAYS EVENT UNARY PASS");
    else $display("ALWAYS EVENT UNARY FAIL");
    $finish;
  end
endmodule
