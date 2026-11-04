// SPDX-License-Identifier: Apache-2.0
// A packed concatenation event applies negedge to its result LSB.
module top;
  logic [1:0] a = 2'b00;
  logic [1:0] b = 2'b01;
  int seen = 0;

  always @(negedge {a, b})
    seen++;

  initial begin
    #1; a = 2'b10;
    #1; b = 2'b00;
    #1; a = 2'b11;
    #1;
    if (seen === 1) $display("ALWAYS EVENT CONCAT NEGEDGE PASS");
    else $display("ALWAYS EVENT CONCAT NEGEDGE FAIL");
    $finish;
  end
endmodule
