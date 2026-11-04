// SPDX-License-Identifier: Apache-2.0
// A direct dynamic packed part-select applies the edge rule to its result LSB.
module top;
  logic [3:0] bus = 4'b0000;
  logic [1:0] base = 2'b00;
  int seen = 0;

  always @(posedge bus[base +: 2])
    seen++;

  initial begin
    #1; bus = 4'b0010;
    #1; bus = 4'b0001;
    #1; base = 2'b01;
    #1; bus = 4'b0101;
    #1; bus = 4'b0111;
    #1;
    if (seen === 2) $display("ALWAYS EVENT DYNAMIC PART SELECT POSEDGE PASS");
    else $display("ALWAYS EVENT DYNAMIC PART SELECT POSEDGE FAIL");
    $finish;
  end
endmodule
