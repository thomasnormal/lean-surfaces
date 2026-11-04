// SPDX-License-Identifier: Apache-2.0
// A scalar conditional event samples the selected branch value.
module top;
  logic sel = 1'b0;
  logic a = 1'b0;
  logic b = 1'b0;
  logic d = 1'b0;
  logic q = 1'b1;

  always @(sel ? a : b)
    q = d;

  initial begin
    #1; b = 1'b1;
    #1;
    if (q === 1'b0) $display("ALWAYS EVENT CONDITIONAL PASS");
    else $display("ALWAYS EVENT CONDITIONAL FAIL");
    $finish;
  end
endmodule
