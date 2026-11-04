// SPDX-License-Identifier: Apache-2.0
// A selected packed clock uses the sampled selected bit's edge.
module top;
  logic [1:0] bus = 2'b00;
  logic q = 1'b0;

  always_ff @(posedge bus[0])
    q <= 1'b1;

  initial begin
    #1; bus = 2'b01;
    #1;
    if (q === 1'b1) $display("ALWAYS_FF SELECTED CLOCK PASS");
    else $display("ALWAYS_FF SELECTED CLOCK FAIL");
    $finish;
  end
endmodule
