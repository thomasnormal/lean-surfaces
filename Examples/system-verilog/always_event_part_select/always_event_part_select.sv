// SPDX-License-Identifier: Apache-2.0
// A constant packed part-select event compares the complete sampled vector.
module top;
  logic [3:0] bus = 4'b0000;
  logic d = 1'b0;
  logic q = 1'b1;

  always @(bus[3:0])
    q = d;

  initial begin
    #1; bus = 4'b0100;
    #1;
    if (q === 1'b0) $display("ALWAYS EVENT PART SELECT PASS");
    else $display("ALWAYS EVENT PART SELECT FAIL");
    $finish;
  end
endmodule
