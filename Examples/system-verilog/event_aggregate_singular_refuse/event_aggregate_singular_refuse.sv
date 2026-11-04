// SPDX-License-Identifier: Apache-2.0
// Recorded boundary: unpacked-array element event needs aggregate storage.
module top;
  logic [7:0] arr[4];
  logic seen;

  always @(arr[2])
    seen = 1'b1;

  initial begin
    #1; arr[2] = 8'hab;
    #1;
    $display("EVENT AGGREGATE REFUSED");
    $finish;
  end
endmodule
