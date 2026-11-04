// SPDX-License-Identifier: Apache-2.0
// A dynamic descending packed part-select is a truthy event guard.
module top;
  logic clk = 1'b0;
  logic [3:0] en = 4'b0000;
  logic [1:0] idx = 2'b01;
  logic d = 1'b0;
  logic q = 1'b1;

  always_ff @(posedge clk iff en[idx -: 2])
    q <= d;

  initial begin
    #1; clk = 1'b1;
    #1; clk = 1'b0; en = 4'b0010;
    #1; clk = 1'b1;
    #1;
    if (q === 1'b0) $display("ALWAYS_FF IFF DYNAMIC NEG PASS");
    else $display("ALWAYS_FF IFF DYNAMIC NEG FAIL");
    $finish;
  end
endmodule
