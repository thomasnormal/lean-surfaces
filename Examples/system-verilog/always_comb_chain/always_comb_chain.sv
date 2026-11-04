// SPDX-License-Identifier: Apache-2.0
// A comb write wakes a dependent comb process in the same time slot.
module top;
  logic [3:0] a = 4'd0;
  logic [3:0] y;
  logic [3:0] z;
  always_comb y = a;
  always_comb z = y;
  initial begin
    #1;
    a = 4'd5;
    #1;
    if (z == 4'd5) $display("ALWAYS_COMB CHAIN PASS");
    else $display("ALWAYS_COMB CHAIN FAIL");
    $finish;
  end
endmodule
