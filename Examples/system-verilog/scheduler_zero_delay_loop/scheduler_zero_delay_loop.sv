// SPDX-License-Identifier: Apache-2.0
// A zero-delay event loop must be bounded, never silently accepted.
module top;
  logic a = 1'b0;
  always @(a) a <= ~a;
  initial begin
    a = 1'b1;
    #1;
    $display("UNREACHED");
    $finish;
  end
endmodule
