// SPDX-License-Identifier: Apache-2.0
// A dynamic packed bit-select is a singular sampled event expression.
module top;
  logic [3:0] bus = 4'b0001;
  logic [1:0] idx = 2'd0;
  int seen = 0;

  always @(bus[idx])
    seen++;

  initial begin
    #1; bus = 4'b0000;
    #1; idx = 2'd1;
    #1; bus = 4'b0010;
    #1;
    if (seen === 2) $display("ALWAYS EVENT DYNAMIC BIT SELECT PASS");
    else $display("ALWAYS EVENT DYNAMIC BIT SELECT FAIL");
    $finish;
  end
endmodule
