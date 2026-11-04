// SPDX-License-Identifier: Apache-2.0
// An always_latch captures two outputs while enabled and holds them disabled.
module top;
  logic en = 1'b0;
  logic [3:0] a = 4'd1;
  logic [3:0] b = 4'd2;
  logic [3:0] q;
  logic [3:0] r;

  always_latch begin
    if (en) begin
      q = a;
      r = b;
    end
  end

  initial begin
    #1;
    en = 1'b1;
    #1;
    if (q == 4'd1 && r == 4'd2)
      $display("ALWAYS_LATCH MULTI CAPTURE PASS");
    else
      $display("ALWAYS_LATCH MULTI CAPTURE FAIL");
    a = 4'd3;
    b = 4'd4;
    #1;
    if (q == 4'd3 && r == 4'd4)
      $display("ALWAYS_LATCH MULTI UPDATE PASS");
    else
      $display("ALWAYS_LATCH MULTI UPDATE FAIL");
    en = 1'b0;
    a = 4'd7;
    b = 4'd8;
    #1;
    if (q == 4'd3 && r == 4'd4)
      $display("ALWAYS_LATCH MULTI HOLD PASS");
    else
      $display("ALWAYS_LATCH MULTI HOLD FAIL");
    $finish;
  end
endmodule
