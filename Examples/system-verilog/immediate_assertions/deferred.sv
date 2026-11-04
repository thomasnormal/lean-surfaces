// SPDX-License-Identifier: Apache-2.0
module top;
  initial begin
    assert #0 (1);
    $display("deferred");
    $finish;
  end
endmodule
