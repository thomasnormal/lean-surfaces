// SPDX-License-Identifier: Apache-2.0
// An always_latch captures while enabled and holds while disabled.
module top;
  logic en = 1'b0;
  logic d = 1'b0;
  logic q;

  always_latch if (en) q = d;

  initial begin
    #1;
    d = 1'b1;
    #1;
    en = 1'b1;
    #1;
    en = 1'b0;
    d = 1'b0;
    #1;
    if (q === 1'b1) $display("ALWAYS_LATCH WAKE PASS");
    else $display("ALWAYS_LATCH WAKE FAIL");
    $finish;
  end
endmodule
