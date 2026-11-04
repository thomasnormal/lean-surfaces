// SPDX-License-Identifier: Apache-2.0
// A zero-delay always procedure has no legal simulation-time control.
module top;
  logic a;
  logic y;

  always y = a;

  initial begin
    a = 1'b0;
    #1;
    $display("UNREACHED");
    $finish;
  end
endmodule
