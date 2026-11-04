// SPDX-License-Identifier: Apache-2.0
// An always_ff process is admitted as a retained positive-edge waiter.
module top;
  logic clk = 1'b0;
  logic d = 1'b1;
  logic q;
  always_ff @(posedge clk) q <= d;
  initial begin
    $display("ALWAYS_FF PASS");
    $finish;
  end
endmodule
