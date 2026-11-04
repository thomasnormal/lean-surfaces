// SPDX-License-Identifier: Apache-2.0
// An NBA publication must wake a same-slot event waiter again.
module top;
  logic clk = 1'b0;
  logic a = 1'b0;
  int seen = 0;
  always @(posedge a) seen++;
  initial begin
    #1;
    a <= 1'b1;
    #1;
    if (seen == 1) $display("SCHED NBA RETRIGGER PASS");
    else $display("SCHED NBA RETRIGGER FAIL");
    $finish;
  end
endmodule
