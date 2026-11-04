// SPDX-License-Identifier: Apache-2.0
// A scalar logical iff guard filters a clocked always_ff edge.
module top;
  logic clk = 1'b0;
  logic en = 1'b0;
  logic mode = 1'b0;
  logic d = 1'b0;
  logic q = 1'b1;

  always_ff @(posedge clk iff en && mode) q <= d;

  initial begin
    #1;
    clk = 1'b1;
    #1;
    clk = 1'b0;
    en = 1'b1;
    mode = 1'b1;
    #1;
    clk = 1'b1;
    #1;
    if (q === 1'b0) $display("ALWAYS_FF IFF LOGIC PASS");
    else $display("ALWAYS_FF IFF LOGIC FAIL");
    $finish;
  end
endmodule
