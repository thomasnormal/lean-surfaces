// SPDX-License-Identifier: Apache-2.0
// A packed asynchronous reset uses the sampled reset result's edge.
module top;
  logic clk = 1'b0;
  logic [1:0] rst = 2'b00;
  logic q = 1'b0;

  always_ff @(posedge clk or posedge rst)
    q <= 1'b1;

  initial begin
    #1; rst = 2'b01;
    #1;
    if (q === 1'b1) $display("ALWAYS_FF VECTOR RESET PASS");
    else $display("ALWAYS_FF VECTOR RESET FAIL");
    $finish;
  end
endmodule
