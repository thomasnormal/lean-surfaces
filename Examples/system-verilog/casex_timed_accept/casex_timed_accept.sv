// SPDX-License-Identifier: Apache-2.0
// Timed self-check casex treats x/z in the selector as wildcards.
module top;
  logic [3:0] a;
  logic y;

  initial begin
    a = 4'b1x01;
    #1;
    casex (a)
      4'b10??: y = 1'b1;
      default: y = 1'b0;
    endcase
    #1;
    if (y === 1'b1) $display("CASEX TIMED PASS");
    else $display("CASEX TIMED FAIL");
    $finish;
  end
endmodule
