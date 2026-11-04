// SPDX-License-Identifier: Apache-2.0
// A sampled constant bit-select event wakes only when that bit changes.
module top;
  logic [3:0] bus = 4'b0000;
  logic d = 1'b0;
  logic q = 1'b1;

  always @(bus[2])
    q = d;

  initial begin
    #1; bus = 4'b0100;
    #1; bus = 4'b0000;
    #1;
    if (q === 1'b0) $display("ALWAYS EVENT BIT SELECT PASS");
    else $display("ALWAYS EVENT BIT SELECT FAIL");
    $finish;
  end
endmodule
