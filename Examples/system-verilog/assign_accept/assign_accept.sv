// SPDX-License-Identifier: Apache-2.0
// A single continuous driver follows a procedural input update.
module top(output logic y);
  logic a;
  assign y = a;
  initial begin
    a = 1'b0;
    #1;
    a = 1'b1;
    #1;
    if (y === 1'b1) $display("ASSIGN PASS");
    else $display("ASSIGN FAIL");
    $finish;
  end
endmodule
