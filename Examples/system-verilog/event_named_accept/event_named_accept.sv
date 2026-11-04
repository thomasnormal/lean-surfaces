// SPDX-License-Identifier: Apache-2.0
// Named event publication and wake-up through the retained scheduler queue.
module top;
  event evt;
  logic seen;

  always @(evt)
    seen = 1'b1;

  initial begin
    #1; -> evt;
    #1;
    $display("NAMED EVENT PASS");
    $finish;
  end
endmodule
