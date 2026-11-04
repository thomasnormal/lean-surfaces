// SPDX-License-Identifier: Apache-2.0
// A dynamic ascending packed part-select is a truthy event guard.
module top;
  logic clk = 1'b0;
  logic [3:0] en = 4'b0000;
  logic [1:0] idx = 2'b00;
  logic d = 1'b0;
  logic q = 1'b1;

  always_ff @(posedge clk iff en[idx +: 2])
    q <= d;

  initial begin
    #1; clk = 1'b1;
    #1; clk = 1'b0; en = 4'b0001;
    #1; clk = 1'b1;
    #1;
    if (q === 1'b0) $display("ALWAYS_FF IFF DYNAMIC PASS");
    else $display("ALWAYS_FF IFF DYNAMIC FAIL");
    $finish;
  end
endmodule
