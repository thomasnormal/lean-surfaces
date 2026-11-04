// SPDX-License-Identifier: Apache-2.0
// A packed vector clock uses the sampled result's least-significant edge.
module top;
  logic [1:0] bus = 2'b00;
  logic q = 1'b0;

  always_ff @(posedge bus)
    q <= 1'b1;

  initial begin
    #1; bus = 2'b01;
    #1;
    if (q === 1'b1) $display("ALWAYS_FF VECTOR CLOCK PASS");
    else $display("ALWAYS_FF VECTOR CLOCK FAIL");
    $finish;
  end
endmodule
