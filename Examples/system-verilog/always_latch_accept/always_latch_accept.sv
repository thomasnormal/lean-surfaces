// SPDX-License-Identifier: Apache-2.0
// An enabled latch captures its data during the initial Active pass.
module top;
  logic en = 1'b1;
  logic d = 1'b1;
  logic q;
  always_latch if (en) q = d;
  initial begin
    #1;
    if (q === 1'b1) $display("ALWAYS_LATCH PASS");
    else $display("ALWAYS_LATCH FAIL");
    $finish;
  end
endmodule
