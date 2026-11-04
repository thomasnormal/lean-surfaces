// SPDX-License-Identifier: Apache-2.0
// Recorded boundary: procedural expression waits need retained suspension state.
module top;
  logic a = 1'b0;
  logic b = 1'b0;
  logic seen;

  initial begin
    @(a ^ b);
    seen = 1'b1;
  end

  initial begin
    #1; a = 1'b1;
    #1;
    $display("PROCEDURAL EXPRESSION WAIT REFUSED");
    $finish;
  end
endmodule
