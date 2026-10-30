// SPDX-License-Identifier: Apache-2.0
// Active blocking writes precede the NBA commit in one time slot.
module top;
  logic [3:0] value;
  initial begin
    #1;
    value = 4'd1;
  end
  initial begin
    #1;
    value <= 4'd2;
  end
  initial begin
    #2;
    if (value == 4'd2) $display("SCHED BLOCKING NBA PASS");
    else $display("SCHED BLOCKING NBA FAIL");
    $finish;
  end
endmodule
