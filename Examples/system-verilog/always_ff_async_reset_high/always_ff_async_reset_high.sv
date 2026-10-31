// SPDX-License-Identifier: Apache-2.0
// An always_ff process responds to a positive-edge asynchronous reset.
module top;
  logic clk = 1'b0;
  logic rst = 1'b0;
  logic d = 1'b0;
  logic q;
  logic seen_reset = 1'b0;

  always_ff @(posedge clk or posedge rst) begin
    if (rst) q <= 1'b0;
    else q <= d;
  end

  initial begin
    #1;
    d = 1'b1;
    #1;
    clk = 1'b1;
    #1;
    clk = 1'b0;
    #1;
    rst = 1'b1;
    #1;
    if (q === 1'b0) seen_reset = 1'b1;
    rst = 1'b0;
    d = 1'b1;
    #1;
    clk = 1'b1;
    #1;
    if (seen_reset && q === 1'b1) $display("ALWAYS_FF RESET HIGH PASS");
    else $display("ALWAYS_FF RESET HIGH FAIL");
    $finish;
  end
endmodule
