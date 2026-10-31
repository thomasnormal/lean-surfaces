// SPDX-License-Identifier: Apache-2.0
// A constant packed-vector select is a truthy event guard.
module top;
  logic clk = 1'b0;
  logic [1:0] en = 2'b00;
  logic d = 1'b0;
  logic q = 1'b1;

  always_ff @(posedge clk iff en[1:0])
    q <= d;

  initial begin
    #1; clk = 1'b1;
    #1; clk = 1'b0; en = 2'b01;
    #1; clk = 1'b1;
    #1;
    if (q === 1'b0) $display("ALWAYS_FF IFF VECTOR PASS");
    else $display("ALWAYS_FF IFF VECTOR FAIL");
    $finish;
  end
endmodule
