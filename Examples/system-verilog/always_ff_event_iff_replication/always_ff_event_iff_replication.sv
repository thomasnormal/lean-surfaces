// SPDX-License-Identifier: Apache-2.0
// A constant replication of a packed scalar is a truthy event guard.
module top;
  logic clk = 1'b0;
  logic en = 1'b0;
  logic d = 1'b0;
  logic q = 1'b1;

  always_ff @(posedge clk iff {2{en}})
    q <= d;

  initial begin
    #1; clk = 1'b1;
    #1; clk = 1'b0; en = 1'b1;
    #1; clk = 1'b1;
    #1;
    if (q === 1'b0) $display("ALWAYS_FF IFF REPLICATION PASS");
    else $display("ALWAYS_FF IFF REPLICATION FAIL");
    $finish;
  end
endmodule
