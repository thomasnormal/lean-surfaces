// SPDX-License-Identifier: Apache-2.0
// Timed initial processes retain local declaration state across a delay.
module top;
  initial begin
    integer tmp;
    tmp = 7;
    #1;
    if (tmp == 7) $display("TIMED LOCAL DECL PASS");
    else $display("TIMED LOCAL DECL FAIL");
    $finish;
  end
endmodule
