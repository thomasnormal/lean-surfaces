// SPDX-License-Identifier: Apache-2.0
// Logical implication lowers to !left || right in the retained guard tier.
module top;
  logic clk = 1'b0;
  logic en = 1'b1;
  logic mode = 1'b0;
  logic d = 1'b0;
  logic q = 1'b1;

  always_ff @(posedge clk iff en -> mode)
    q <= d;

  initial begin
    #1; clk = 1'b1;
    #1; clk = 1'b0; en = 1'b0;
    #1; clk = 1'b1;
    #1;
    if (q === 1'b0) $display("ALWAYS_FF IFF IMPLICATION PASS");
    else $display("ALWAYS_FF IFF IMPLICATION FAIL");
    $finish;
  end
endmodule
