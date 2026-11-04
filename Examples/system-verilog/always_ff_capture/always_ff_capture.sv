// SPDX-License-Identifier: Apache-2.0
// An always_ff process captures data on each positive clock edge.
module top;
  logic clk = 1'b0;
  logic d = 1'b0;
  logic q;

  always_ff @(posedge clk) q <= d;

  initial begin
    #1;
    d = 1'b1;
    clk = 1'b1;
    #0;
    clk = 1'b0;
    #1;
    d = 1'b0;
    clk = 1'b1;
    #0;
    clk = 1'b0;
    #1;
    if (q === 1'b0) $display("ALWAYS_FF CAPTURE PASS");
    else $display("ALWAYS_FF CAPTURE FAIL");
    $finish;
  end
endmodule
