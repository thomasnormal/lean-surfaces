// SPDX-License-Identifier: Apache-2.0
// A plain always process may wait on one bare signal.
module top;
  logic trigger = 1'b0;
  int seen = 0;

  always @(trigger) seen++;

  initial begin
    #1;
    trigger = 1'b1;
    #1;
    if (seen == 1) $display("BARE EVENT PASS");
    else $display("BARE EVENT FAIL");
    $finish;
  end
endmodule
