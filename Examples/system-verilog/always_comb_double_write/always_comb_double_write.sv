// SPDX-License-Identifier: Apache-2.0
// Two blocking publications in one Active process must wake always_comb
// through the existing sensitivity queue, with the final value observed.
module top;
  logic a = 1'b0;
  logic y;

  always_comb y = a;

  initial begin
    a = 1'b1;
    a = 1'b0;
    #1;
    if (y == 1'b0) $display("ALWAYS_COMB DOUBLE PASS");
    else $display("ALWAYS_COMB DOUBLE FAIL");
    $finish;
  end
endmodule
