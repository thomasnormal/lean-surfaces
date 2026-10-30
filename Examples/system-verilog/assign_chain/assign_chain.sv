// SPDX-License-Identifier: Apache-2.0
// Continuous assignments propagate through the same Active wake queue.
module top(output logic y);
  logic a;
  wire mid;
  assign mid = a;
  assign y = mid;
  initial begin
    a = 1'b0;
    #1;
    a = 1'b1;
    #1;
    if (y === 1'b1) $display("ASSIGN_CHAIN PASS");
    else $display("ASSIGN_CHAIN FAIL");
    $finish;
  end
endmodule
