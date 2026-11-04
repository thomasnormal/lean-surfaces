// SPDX-License-Identifier: Apache-2.0
// Recorded boundary: chandle values are forbidden in event expressions.
module top;
  chandle h;
  logic seen;

  always @(h)
    seen = 1'b1;

  initial begin
    #1;
    $display("CHANDLE EVENT REFUSED");
    $finish;
  end
endmodule
