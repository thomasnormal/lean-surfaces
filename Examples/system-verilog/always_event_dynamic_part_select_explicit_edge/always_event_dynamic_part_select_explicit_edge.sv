// SPDX-License-Identifier: Apache-2.0
// Explicit edge on a dynamic packed part-select uses any result change.
module top;
  logic [3:0] bus = 4'b0000;
  logic [1:0] base = 2'b00;
  int seen = 0;

  always @(edge bus[base +: 2])
    seen++;

  initial begin
    #1; bus = 4'b0001;
    #1; bus = 4'b0011;
    #1; base = 2'b01;
    #1; bus = 4'b0111;
    #1; bus = 4'b0101;
    #1;
    if (seen === 5) $display("ALWAYS EVENT DYNAMIC PART SELECT EXPLICIT EDGE PASS");
    else $display("ALWAYS EVENT DYNAMIC PART SELECT EXPLICIT EDGE FAIL");
    $finish;
  end
endmodule
