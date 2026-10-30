// SPDX-License-Identifier: Apache-2.0
// Initial and always processes share delayed time slots.
module top;
  int ticks = 0;
  always begin
    #1;
    ticks++;
  end
  initial begin
    #2;
    if (ticks == 2) $display("SCHED INITIAL ALWAYS PASS");
    else $display("SCHED INITIAL ALWAYS FAIL");
    $finish;
  end
endmodule
