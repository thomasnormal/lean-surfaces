// SPDX-License-Identifier: Apache-2.0
// A scalar iff guard filters a negative-edge clocked always_ff edge.
module top;
  logic clk = 1'b1;
  logic en = 1'b0;
  logic d = 1'b0;
  logic q = 1'b1;

  always_ff @(negedge clk iff en) q <= d;

  initial begin
    #1;
    clk = 1'b0;
    #1;
    clk = 1'b1;
    en = 1'b1;
    d = 1'b0;
    #1;
    clk = 1'b0;
    #1;
    if (q === 1'b0) $display("ALWAYS_FF NEG IFF PASS");
    else $display("ALWAYS_FF NEG IFF FAIL");
    $finish;
  end
endmodule
