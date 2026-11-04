// SPDX-License-Identifier: Apache-2.0
// A scalar iff guard qualifies the asynchronous reset edge itself.
module top;
  logic clk = 1'b0;
  logic rst_n = 1'b1;
  logic en = 1'b0;
  logic d = 1'b1;
  logic q = 1'b1;

  always_ff @(posedge clk or negedge rst_n iff en)
    if (!rst_n) q <= 1'b0;
    else q <= d;

  initial begin
    #1; clk = 1'b1;
    #1; clk = 1'b0; rst_n = 1'b0;
    #1; rst_n = 1'b1; en = 1'b1;
    #1; rst_n = 1'b0;
    #1;
    if (q === 1'b0) $display("ALWAYS_FF RESET IFF RESET PASS");
    else $display("ALWAYS_FF RESET IFF RESET FAIL");
    $finish;
  end
endmodule
