// SPDX-License-Identifier: Apache-2.0
// A packed vector edge is detected only on its least-significant bit.
module top;
  logic [3:0] bus = 4'b0000;
  int edge_count = 0;

  always @(posedge bus)
    edge_count++;

  initial begin
    #1; bus = 4'b0010;
    #1; bus = 4'b0001;
    #1; bus = 4'b0011;
    #1;
    if (edge_count === 1) $display("ALWAYS EVENT MULTIBIT POSEDGE PASS");
    else $display("ALWAYS EVENT MULTIBIT POSEDGE FAIL");
    $finish;
  end
endmodule
