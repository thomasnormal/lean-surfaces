// SPDX-License-Identifier: Apache-2.0
module top;
  logic gate = 1'bx;
  logic trigger;
  int choice = 0;
  int event_tail = 0;
  initial begin
    assert (gate) begin #2; choice=11; end
      else begin #3; choice=22; end
    $display("failure_tail %0d live %b",choice,gate);
    assume (gate) begin #2; choice=33; end
      else begin #3; choice=44; end
    $display("success_tail %0d live %b",choice,gate);
    $finish;
  end
  initial begin
    #1 gate=1;
    #3 gate=0;
  end
  initial begin
    cover (1) begin @(trigger); event_tail=1; end
  end
endmodule
