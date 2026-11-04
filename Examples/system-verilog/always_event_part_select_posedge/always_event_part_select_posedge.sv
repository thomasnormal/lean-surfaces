// SPDX-License-Identifier: Apache-2.0
// A constant packed part-select event applies posedge to its sampled LSB.
module top;
  logic [3:0] bus = 4'b0000;
  logic seen = 1'b0;

  always @(posedge bus[3:0])
    seen = 1'b1;

  initial begin
    #1; bus = 4'b0100;
    #1; bus = 4'b0101;
    #1;
    if (seen === 1'b1) $display("ALWAYS EVENT PART SELECT POSEDGE PASS");
    else $display("ALWAYS EVENT PART SELECT POSEDGE FAIL");
    $finish;
  end
endmodule
