// SPDX-License-Identifier: Apache-2.0
// The timed loader must refuse until procedural writes publish each edge.
module top;
  logic trigger = 0;
  int changes = 0;
  int falls = 0;
  always @(trigger) changes++;
  always @(negedge trigger) falls++;
  initial begin
    #1 trigger=1;
    #1 trigger=0;
    #1;
    $display("edges %0d %0d",changes,falls);
    $finish;
  end
endmodule
