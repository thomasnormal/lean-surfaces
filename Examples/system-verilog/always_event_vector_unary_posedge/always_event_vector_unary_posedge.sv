// SPDX-License-Identifier: Apache-2.0
// A vector bitwise-not event applies posedge to its sampled result LSB.
module top;
  logic [1:0] bus = 2'b00;
  int seen = 0;

  always @(posedge ~bus)
    seen++;

  initial begin
    #1; bus = 2'b01;
    #1; bus = 2'b00;
    #1; bus = 2'b10;
    #1; bus = 2'b11;
    #1; bus = 2'b00;
    #1;
    if (seen === 2) $display("ALWAYS EVENT VECTOR UNARY POSEDGE PASS");
    else $display("ALWAYS EVENT VECTOR UNARY POSEDGE FAIL");
    $finish;
  end
endmodule
