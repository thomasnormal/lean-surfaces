// SPDX-License-Identifier: Apache-2.0
// Two ordinary wire drivers resolve from live source values in one time slot.
module top;
  logic a = 1'b0;
  logic b = 1'b1;
  wire y;

  assign y = a;
  assign y = b;

  initial begin
    // Compound writes keep these sources live for the continuous-driver
    // admission check while preserving their declaration values.
    a += 1'b0;
    b += 1'b0;
    #1;
    if (y === 1'bx) $display("NET RESOLUTION PASS");
    else $display("NET RESOLUTION FAIL");
    $finish;
  end
endmodule
