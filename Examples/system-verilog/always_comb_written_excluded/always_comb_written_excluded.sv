// SPDX-License-Identifier: Apache-2.0
// A variable written by always_comb is excluded from implicit sensitivity.
module top;
  logic [3:0] a = 4'd0;
  logic [3:0] y;
  always_comb begin
    y = a;
    a = y;
  end
  initial begin
    #1;
    a = 4'd3;
    #1;
    if (y == 4'd0) $display("ALWAYS_COMB EXCLUDE PASS");
    else $display("ALWAYS_COMB EXCLUDE FAIL");
    $finish;
  end
endmodule
