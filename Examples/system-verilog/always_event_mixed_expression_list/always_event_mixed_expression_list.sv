// SPDX-License-Identifier: Apache-2.0
// A mixed event list retains expression and scalar registrations together.
module top;
  logic [1:0] a = 2'b00;
  logic [1:0] b = 2'b01;
  logic c = 1'b0;
  int seen = 0;
  int baseline;

  always @(a | b or c)
    seen++;

  initial begin
    #1; baseline = seen;
    a = 2'b10;
    #1; c = 1'b1;
    #1; b = 2'b11;
    #1;
    if (seen === baseline + 3)
      $display("ALWAYS EVENT MIXED LIST PASS");
    else
      $display("ALWAYS EVENT MIXED LIST FAIL");
    $finish;
  end
endmodule
