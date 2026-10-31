// SPDX-License-Identifier: Apache-2.0
// A plain always event list wakes when either listed signal changes.
module top;
  logic a = 1'b0;
  logic b = 1'b0;
  logic y = 1'b0;

  always @(a or b) y = a ^ b;

  initial begin
    #1;
    a = 1'b1;
    #1;
    if (y === 1'b1) $display("EVENT LIST PASS");
    else $display("EVENT LIST FAIL");
    $finish;
  end
endmodule
