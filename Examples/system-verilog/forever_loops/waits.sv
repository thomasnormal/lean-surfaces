// SPDX-License-Identifier: Apache-2.0
// A permanent event wait is retained; it is not an empty iteration.
module top;
  logic trigger;
  int visits = 0;
  initial forever @(posedge trigger);
  initial begin
    #2;
    $display("blocked %0d", visits);
    $finish;
  end
endmodule
