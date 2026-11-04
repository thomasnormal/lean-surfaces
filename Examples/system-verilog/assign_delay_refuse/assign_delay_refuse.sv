// SPDX-License-Identifier: Apache-2.0
// Delayed continuous publication remains outside the retained timed driver.
module top;
  logic a;
  wire y;

  assign #1 y = a;

  initial begin
    a = 1'b0;
    #1;
    a = 1'b1;
    #2;
    $display("UNREACHED");
    $finish;
  end
endmodule
