// SPDX-License-Identifier: Apache-2.0
// Bitwise-not applies to an admitted packed vector event guard.
module top;
  logic clk = 1'b0;
  logic [1:0] en = 2'b11;
  logic d = 1'b0;
  logic q = 1'b1;

  always_ff @(posedge clk iff ~en[1:0])
    q <= d;

  initial begin
    #1; clk = 1'b1;
    #1; clk = 1'b0; en = 2'b00;
    #1; clk = 1'b1;
    #1;
    if (q === 1'b0) $display("ALWAYS_FF IFF VECTOR BNOT PASS");
    else $display("ALWAYS_FF IFF VECTOR BNOT FAIL");
    $finish;
  end
endmodule
