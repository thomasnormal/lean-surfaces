// SPDX-License-Identifier: Apache-2.0
// A timed strobe is evaluated in the Postponed region after Active writes.
/*
:name: scheduler_postponed_strobe
:description: IEEE 1800-2023 Section 21.2 -- timed $strobe observes the
  final value after the Active region closes.
:tags: 4.4 21.2
:type: simulation
// Expected transcript: SCHED DISPLAY; SCHED STROBE 9.
*/
module top;
  integer a;
  initial begin
    a = 4;
    $display("SCHED DISPLAY");
    $strobe("SCHED STROBE %0d", a);
    a = 9;
    #1 $finish;
  end
endmodule
