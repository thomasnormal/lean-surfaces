// SPDX-License-Identifier: Apache-2.0
// Timed self-check cases retain casez wildcard matching.
module top;
  logic [3:0] a;
  logic y;

  initial begin
    a = 4'b1001;
    #1;
    casez (a)
      4'b1???: y = 1'b1;
      default: y = 1'b0;
    endcase
    #1;
    if (y === 1'b1) $display("CASEZ TIMED PASS");
    else $display("CASEZ TIMED FAIL");
    $finish;
  end
endmodule
