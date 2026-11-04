// SPDX-License-Identifier: Apache-2.0
// A source with no event occurrence remains blocked until another process finishes.
module top;
  logic trigger;
  int changes = 0;
  int falls = 0;
  always @(trigger) changes++;
  always @(negedge trigger) falls++;
  initial begin
    #2;
    $display("waiting %0d %0d",changes,falls);
    $finish;
  end
endmodule
