// SPDX-License-Identifier: Apache-2.0
// A constant bit-select may be the sampled source of an edge event.
module top;
  logic [3:0] bus = 4'b0000;
  logic d = 1'b0;
  logic q = 1'b1;

  always @(posedge bus[2])
    q = d;

  initial begin
    #1; bus = 4'b0100;
    #1;
    if (q === 1'b0) $display("ALWAYS EVENT BIT SELECT POSEDGE PASS");
    else $display("ALWAYS EVENT BIT SELECT POSEDGE FAIL");
    $finish;
  end
endmodule
