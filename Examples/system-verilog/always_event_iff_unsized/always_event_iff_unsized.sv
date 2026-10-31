// SPDX-License-Identifier: Apache-2.0
// Unsized scalar comparisons retain their expression-context resize in iff guards.
module top;
  logic clk = 1'b0;
  logic en = 1'b0;
  logic d = 1'b0;
  logic q = 1'b1;

  always @(posedge clk iff en == 1)
    q = d;

  initial begin
    #1; clk = 1'b1;
    #1; clk = 1'b0; en = 1'b1;
    #1; clk = 1'b1;
    #1;
    if (q === 1'b0) $display("ALWAYS IFF UNSIZED PASS");
    else $display("ALWAYS IFF UNSIZED FAIL");
    $finish;
  end
endmodule
