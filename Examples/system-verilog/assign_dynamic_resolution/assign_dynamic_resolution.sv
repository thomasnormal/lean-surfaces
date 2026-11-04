// SPDX-License-Identifier: Apache-2.0
// Multiple whole-net drivers resolve again after each live source update.
module top;
  logic a = 1'b0;
  logic b = 1'b0;
  wire y;

  assign y = a;
  assign y = b;

  initial begin
    #1;
    if (y === 1'b0) $display("DYNAMIC RESOLUTION ZERO PASS");
    else $display("DYNAMIC RESOLUTION ZERO FAIL");
    a = 1'b1;
    #1;
    if (y === 1'bx) $display("DYNAMIC RESOLUTION CONFLICT PASS");
    else $display("DYNAMIC RESOLUTION CONFLICT FAIL");
    b = 1'b1;
    #1;
    if (y === 1'b1) $display("DYNAMIC RESOLUTION ONE PASS");
    else $display("DYNAMIC RESOLUTION ONE FAIL");
    a = 1'b0;
    b = 1'b0;
    #1;
    if (y === 1'b0) $display("DYNAMIC RESOLUTION RETURN PASS");
    else $display("DYNAMIC RESOLUTION RETURN FAIL");
    $finish;
  end
endmodule
