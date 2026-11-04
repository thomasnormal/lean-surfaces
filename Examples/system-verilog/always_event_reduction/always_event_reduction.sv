// SPDX-License-Identifier: Apache-2.0
// A reduction event compares the scalar reduction result.
module top;
  logic [3:0] v = 4'b0000;
  logic d = 1'b0;
  logic q = 1'b1;

  always @(|v)
    q = d;

  initial begin
    #1; v = 4'b0100;
    #1; v = 4'b0110;
    #1; v = 4'b0000;
    #1;
    if (q === 1'b0) $display("ALWAYS EVENT REDUCTION PASS");
    else $display("ALWAYS EVENT REDUCTION FAIL");
    $finish;
  end
endmodule
