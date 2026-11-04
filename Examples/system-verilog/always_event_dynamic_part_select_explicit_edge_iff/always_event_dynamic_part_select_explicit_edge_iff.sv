// SPDX-License-Identifier: Apache-2.0
// Explicit edge and iff guard apply to a dynamic packed part-select.
module top;
  logic [3:0] bus = 4'b0000;
  logic [1:0] base = 2'b00;
  logic en = 1'b0;
  int seen = 0;

  always @(edge bus[base +: 2] iff en)
    seen++;

  initial begin
    #1; bus = 4'b0001;
    #1; en = 1'b1;
    #1; bus = 4'b0011;
    #1; base = 2'b01;
    #1; bus = 4'b0111;
    #1;
    if (seen === 3) $display("ALWAYS EVENT DYNAMIC PART SELECT EXPLICIT EDGE IFF PASS");
    else $display("ALWAYS EVENT DYNAMIC PART SELECT EXPLICIT EDGE IFF FAIL");
    $finish;
  end
endmodule
