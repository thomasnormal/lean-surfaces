// SPDX-License-Identifier: Apache-2.0
// @* and posedge waits both need publication when a signal changes twice.
module top;
  logic clk = 1'b0;
  logic a = 1'b0;
  int seen = 0;
  always @* a = clk;
  always @(posedge clk) seen++;
  initial begin
    #1;
    clk = 1'b1;
    clk = 1'b0;
    clk = 1'b1;
    #1;
    if (seen == 2 && a == 1'b1) $display("SCHED SENS PASS");
    else $display("SCHED SENS FAIL");
    $finish;
  end
endmodule
