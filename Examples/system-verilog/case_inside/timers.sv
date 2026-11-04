// SPDX-License-Identifier: Apache-2.0
// Selected wildcard/range arms survive changes to the subject and endpoints.
module top;
  logic [3:0] selector = 4'bx001;
  logic [3:0] candidate = 4'b0001;
  logic [3:0] mask = 4'bz001;
  int choice = 0;
  int value = 5;
  int lo = 1;
  int hi = 9;
  initial begin
    case(selector) inside
      candidate: choice=1;
      mask: begin #2; choice=2; end
      default: choice=3;
    endcase
    $display("wildcard %0d live %b",choice,selector);
    case(value) inside
      [lo:hi]: begin #2; choice=4; end
      default: choice=5;
    endcase
    $display("range %0d live %0d %0d %0d",choice,value,lo,hi);
    case(value) inside [lo:hi]: choice=6; default: choice=7; endcase
    $display("reentry %0d",choice);
    $finish;
  end
  initial begin
    #1 selector=4'b1110;
    #2 value=20;
    lo=30; hi=40;
  end
endmodule
