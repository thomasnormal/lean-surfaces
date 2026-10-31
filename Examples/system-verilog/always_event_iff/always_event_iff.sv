// SPDX-License-Identifier: Apache-2.0
// A scalar iff guard filters the edge at publication time.
module top;
  logic clk = 1'b0;
  logic en = 1'b0;
  logic q = 1'b0;

  always @(posedge clk iff en) q = 1'b1;

  initial begin
    #1;
    clk = 1'b1;
    #1;
    clk = 1'b0;
    en = 1'b1;
    #1;
    clk = 1'b1;
    #1;
    if (q === 1'b1) $display("EVENT IFF PASS");
    else $display("EVENT IFF FAIL");
    $finish;
  end
endmodule
