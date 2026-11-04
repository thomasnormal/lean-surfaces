// SPDX-License-Identifier: Apache-2.0
// Dynamic selected continuous targets remain outside the per-bit driver tier.
module top;
  logic a;
  wire [1:0] y;

  assign y[a] = a;

  initial begin
    a = 1'b0;
    #1;
    a = 1'b1;
    #1;
    $display("UNREACHED");
    $finish;
  end
endmodule
