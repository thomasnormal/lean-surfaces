// SPDX-License-Identifier: Apache-2.0
// A ternary packed event applies posedge to the sampled result's LSB.
module top;
  logic sel = 1'b0;
  logic [1:0] a = 2'b00;
  logic [1:0] b = 2'b00;
  int seen = 0;

  always @(posedge (sel ? a : b))
    seen++;

  initial begin
    #1; b = 2'b10;
    #1; b = 2'b01;
    #1; sel = 1'b1;
    #1; a = 2'b11;
    #1;
    if (seen === 2) $display("ALWAYS EVENT TERNARY POSEDGE PASS");
    else $display("ALWAYS EVENT TERNARY POSEDGE FAIL");
    $finish;
  end
endmodule
