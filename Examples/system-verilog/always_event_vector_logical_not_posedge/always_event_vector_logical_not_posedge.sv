// SPDX-License-Identifier: Apache-2.0
// A vector logical-not event applies posedge to its scalar result.
module top;
  logic [1:0] bus = 2'b01;
  int seen = 0;

  always @(posedge !bus)
    seen++;

  initial begin
    #1; bus = 2'b00;
    #1; bus = 2'b10;
    #1; bus = 2'b00;
    #1;
    if (seen === 2) $display("ALWAYS EVENT VECTOR NOT POSEDGE PASS");
    else $display("ALWAYS EVENT VECTOR NOT POSEDGE FAIL");
    $finish;
  end
endmodule
