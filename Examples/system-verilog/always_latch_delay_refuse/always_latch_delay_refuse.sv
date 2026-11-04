// SPDX-License-Identifier: Apache-2.0
// always_latch cannot suspend on a timing control in the comb settle path.
module top;
  logic en;
  logic a;
  logic q;

  always_latch begin
    #1;
    if (en) q = a;
  end

  initial begin
    en = 1'b1;
    a = 1'b0;
    #2;
    $display("UNREACHED");
    $finish;
  end
endmodule
