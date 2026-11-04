// SPDX-License-Identifier: Apache-2.0
// An NBA publication wakes the implicit-sensitivity process after commit.
module top;
  logic [3:0] a = 4'd0;
  logic [3:0] y;
  always_comb y = a;
  initial begin
    #1;
    a <= 4'd3;
    #1;
    if (y == 4'd3) $display("ALWAYS_COMB NBA PASS");
    else $display("ALWAYS_COMB NBA FAIL");
    $finish;
  end
endmodule
