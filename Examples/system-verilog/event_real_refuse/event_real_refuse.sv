// SPDX-License-Identifier: Apache-2.0
// Recorded boundary: real event values have no represented storage/equality.
module top;
  real r = 0.0;
  logic seen;

  always @(r)
    seen = 1'b1;

  initial begin
    #1; r = 1.5;
    #1;
    $display("REAL EVENT REFUSED");
    $finish;
  end
endmodule
