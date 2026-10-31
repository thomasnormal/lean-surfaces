// SPDX-License-Identifier: Apache-2.0
// A bit-select guard qualifies only the clock event; reset remains unguarded.
module top;
  logic clk = 1'b0;
  logic rst_n = 1'b1;
  logic [1:0] en = 2'b00;
  logic d = 1'b0;
  logic q = 1'b1;

  always_ff @(posedge clk iff en[0] or negedge rst_n)
    if (!rst_n) q <= 1'b0;
    else q <= d;

  initial begin
    #1; clk = 1'b1;
    #1; clk = 1'b0; rst_n = 1'b0;
    #1; rst_n = 1'b1; en[0] = 1'b1;
    #1; clk = 1'b1;
    #1;
    if (q === 1'b0) $display("ALWAYS_FF RESET IFF BIT PASS");
    else $display("ALWAYS_FF RESET IFF BIT FAIL");
    $finish;
  end
endmodule
