// SPDX-License-Identifier: Apache-2.0
module top;
  logic a = 1'b0;
  logic b = 1'b0;
  logic seen;

  initial begin
    @(a ^ b);
    seen = 1'b1;
    $display("PROCEDURAL EXPRESSION WAIT PASS");
    $finish;
  end

  initial begin
    #1; a = 1'b1;
  end
endmodule
