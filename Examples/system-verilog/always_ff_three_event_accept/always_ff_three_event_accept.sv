// SPDX-License-Identifier: Apache-2.0
// A multi-source always_ff control retains all sampled event members.
module top;
  logic clk = 1'b0;
  logic rst = 1'b0;
  logic alt = 1'b1;
  logic d = 1'b1;
  logic q = 1'b0;

  always_ff @(posedge clk or posedge rst or negedge alt)
    q <= d;

  initial begin
    #1; clk = 1'b1;
    #1; clk = 1'b0; rst = 1'b1;
    #1; alt = 1'b0;
    #1;
    if (q === 1'b1) $display("ALWAYS_FF THREE EVENT PASS");
    else $display("ALWAYS_FF THREE EVENT FAIL");
    $finish;
  end
endmodule
