// SPDX-License-Identifier: Apache-2.0
// A literal packed bit continuous driver contributes z outside its window.
// Y=z0
// Y=z1
module top;
  logic a;
  wire [1:0] y;

  assign y[0] = a;

  initial begin
    a = 1'b0;
    #1;
    $display("Y=%b", y);
    a = 1'b1;
    #1;
    $display("Y=%b", y);
    $finish;
  end
endmodule
