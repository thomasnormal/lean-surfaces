// SPDX-License-Identifier: Apache-2.0
// The clock event is guarded; the asynchronous reset event is not.
module top;
  logic clk = 1'b0;
  logic rst_n = 1'b1;
  logic en = 1'b0;
  logic d = 1'b0;
  logic q = 1'b1;

  always_ff @(posedge clk iff en or negedge rst_n)
    if (!rst_n) q <= 1'b0;
    else q <= d;

  initial begin
    #1; clk = 1'b1;
    #1; clk = 1'b0; rst_n = 1'b0;
    #1; rst_n = 1'b1; en = 1'b1;
    #1; clk = 1'b1;
    #1;
    if (q === 1'b0) $display("ALWAYS_FF RESET IFF PASS");
    else $display("ALWAYS_FF RESET IFF FAIL");
    $finish;
  end
endmodule
