// SPDX-License-Identifier: Apache-2.0
// A reduction event applies posedge to its scalar reduction result.
module top;
  logic [1:0] bus = 2'b00;
  int seen = 0;

  always @(posedge |bus)
    seen++;

  initial begin
    #1; bus = 2'b10;
    #1; bus = 2'b11;
    #1; bus = 2'b00;
    #1;
    if (seen === 1) $display("ALWAYS EVENT REDUCTION POSEDGE PASS");
    else $display("ALWAYS EVENT REDUCTION POSEDGE FAIL");
    $finish;
  end
endmodule
