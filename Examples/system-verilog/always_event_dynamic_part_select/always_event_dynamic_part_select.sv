// SPDX-License-Identifier: Apache-2.0
// A direct dynamic packed part-select is a sampled event expression.
module top;
  logic [7:0] bus = 8'b0000_0001;
  logic [2:0] base = 3'd0;
  int seen = 0;
  int baseline;

  always @(bus[base +: 2])
    seen++;

  initial begin
    #1; baseline = seen;
    bus = 8'b0000_0010;
    #1; base = 3'd2;
    #1; bus = 8'b0000_1010;
    #1;
    if (seen === baseline + 3)
      $display("ALWAYS EVENT DYNAMIC PART SELECT PASS");
    else
      $display("ALWAYS EVENT DYNAMIC PART SELECT FAIL");
    $finish;
  end
endmodule
