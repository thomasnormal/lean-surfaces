// SPDX-License-Identifier: Apache-2.0
// Active, postponed, and monitor output need distinct scheduler regions.
// Expected transcript:
// SCHED DISPLAY
// SCHED MONITOR 0
// SCHED STROBE
// SCHED MONITOR 1
module top;
  logic a = 1'b0;
  initial begin
    $monitor("SCHED MONITOR %0d", a);
    $display("SCHED DISPLAY");
    $strobe("SCHED STROBE");
    #1 a = 1'b1;
    #1 $finish;
  end
endmodule
