// SPDX-License-Identifier: Apache-2.0
// always_comb cannot suspend on a timing control in the retained comb path.
module top;
  logic a;
  logic y;

  always_comb begin
    #1;
    y = a;
  end

  initial begin
    a = 1'b0;
    #2;
    $display("UNREACHED");
    $finish;
  end
endmodule
