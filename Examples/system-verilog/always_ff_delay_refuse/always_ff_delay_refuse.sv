// SPDX-License-Identifier: Apache-2.0
// A clocked always_ff body cannot suspend on a timing control.
module top;
  logic clk = 1'b0;
  logic d = 1'b1;
  logic q;

  always_ff @(posedge clk) begin
    #1;
    q <= d;
  end

  initial begin
    #1;
    clk = 1'b1;
    #2;
    $display("UNREACHED");
    $finish;
  end
endmodule
