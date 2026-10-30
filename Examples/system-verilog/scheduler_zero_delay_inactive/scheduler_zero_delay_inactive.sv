// SPDX-License-Identifier: Apache-2.0
// IEEE inactive-region witness: #0 must run after the active region.
module top;
  initial begin
    #0;
    $display("SCHED ZERO PASS");
    $finish;
  end
endmodule
