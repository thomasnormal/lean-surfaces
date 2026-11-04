// SPDX-License-Identifier: Apache-2.0
// An inferred-sensitivity always_comb wakes after a source signal changes.
module top;
  int a = 0;
  int y;
  always_comb y = a;
  initial begin
    #1;
    a = 3;
    #1;
    if (y == 3)
      $display("ALWAYS_COMB PASS");
    else
      $display("ALWAYS_COMB FAIL");
    $finish;
  end
endmodule
