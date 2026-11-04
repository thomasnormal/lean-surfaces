// SPDX-License-Identifier: Apache-2.0
// A packed binary event applies posedge to the sampled result's LSB.
module top;
  logic [1:0] a = 2'b00;
  logic [1:0] b = 2'b00;
  int seen = 0;

  always @(posedge (a | b))
    seen++;

  initial begin
    #1; a = 2'b10;
    #1; b = 2'b01;
    #1; a = 2'b11;
    #1;
    if (seen === 1) $display("ALWAYS EVENT BINARY POSEDGE PASS");
    else $display("ALWAYS EVENT BINARY POSEDGE FAIL");
    $finish;
  end
endmodule
