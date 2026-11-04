// SPDX-License-Identifier: Apache-2.0
// The timed statement runner retains a bounded procedural for loop.
module top;
  integer i;
  integer sum;

  initial begin
    sum = 0;
    i = 0;
    #1;
    for (i = 0; i < 4; i = i + 1)
      sum = sum + i;
    #1;
    if (sum == 6) $display("TIMED FOR PASS");
    else $display("TIMED FOR FAIL");
    $finish;
  end
endmodule
