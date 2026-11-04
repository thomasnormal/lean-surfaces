// SPDX-License-Identifier: Apache-2.0
// A scalar comparison iff guard filters a clocked always_ff edge.
module top;
  logic clk = 1'b0;
  logic en = 1'b0;
  logic d = 1'b0;
  logic q = 1'b1;

  always_ff @(posedge clk iff en == 1'b1) q <= d;

  initial begin
    #1;
    clk = 1'b1;
    #1;
    clk = 1'b0;
    en = 1'b1;
    #1;
    clk = 1'b1;
    #1;
    if (q === 1'b0) $display("ALWAYS_FF IFF CMP PASS");
    else $display("ALWAYS_FF IFF CMP FAIL");
    $finish;
  end
endmodule
