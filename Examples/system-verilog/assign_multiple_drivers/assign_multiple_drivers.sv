// SPDX-License-Identifier: Apache-2.0
// Multiple continuous drivers stay loud until net resolution is modelled.
module top(input logic a, input logic b, output wire y);
  assign y = a;
  assign y = b;
  initial begin
    #1;
    $display("UNREACHED");
    $finish;
  end
endmodule
