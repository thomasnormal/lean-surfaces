// SPDX-License-Identifier: Apache-2.0
// An always_ff process responds to both a clock edge and an async reset edge.
module top;
  logic clk = 1'b0;
  logic rst_n = 1'b1;
  logic d = 1'b1;
  logic q;
  logic seen_reset = 1'b0;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) q <= 1'b0;
    else q <= d;
  end

  initial begin
    #1;
    clk = 1'b1;
    #0;
    clk = 1'b0;
    #1;
    rst_n = 1'b0;
    #1;
    if (q === 1'b0) seen_reset = 1'b1;
    rst_n = 1'b1;
    d = 1'b1;
    #1;
    clk = 1'b1;
    #0;
    clk = 1'b0;
    #1;
    if (q === 1'b1) $display("ALWAYS_FF RESET PASS");
    else $display("ALWAYS_FF RESET FAIL 1");
    $finish;
  end
endmodule
