// SPDX-License-Identifier: Apache-2.0
// An always_ff process captures data on each negative clock edge.
module top;
  logic clk = 1'b1;
  logic d = 1'b0;
  logic q;
  logic first_seen = 1'b0;

  always_ff @(negedge clk) q <= d;

  initial begin
    #1;
    d = 1'b1;
    #1;
    clk = 1'b0;
    #1;
    if (q === 1'b1) first_seen = 1'b1;
    clk = 1'b1;
    #1;
    d = 1'b0;
    clk = 1'b0;
    #1;
    if (first_seen && q === 1'b0) $display("ALWAYS_FF NEGEDGE PASS");
    else $display("ALWAYS_FF NEGEDGE FAIL");
    $finish;
  end
endmodule
