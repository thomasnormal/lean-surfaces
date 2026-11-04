// SPDX-License-Identifier: Apache-2.0
// A branching always_comb process publishes two outputs on each wake.
module top;
  logic sel = 1'b0;
  logic [3:0] a = 4'd1;
  logic [3:0] b = 4'd2;
  logic [3:0] y;
  logic [3:0] z;

  always_comb begin
    if (sel) begin
      y = a;
      z = b;
    end else begin
      y = b;
      z = a;
    end
  end

  initial begin
    #1;
    if (y == 4'd2 && z == 4'd1)
      $display("ALWAYS_COMB BRANCH INITIAL PASS");
    else
      $display("ALWAYS_COMB BRANCH INITIAL FAIL");
    sel = 1'b1;
    #1;
    if (y == 4'd1 && z == 4'd2)
      $display("ALWAYS_COMB BRANCH SELECT PASS");
    else
      $display("ALWAYS_COMB BRANCH SELECT FAIL");
    a = 4'd3;
    b = 4'd4;
    #1;
    if (y == 4'd3 && z == 4'd4)
      $display("ALWAYS_COMB BRANCH DATA PASS");
    else
      $display("ALWAYS_COMB BRANCH DATA FAIL");
    $finish;
  end
endmodule
