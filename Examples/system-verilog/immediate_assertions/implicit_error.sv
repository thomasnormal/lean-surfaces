// SPDX-License-Identifier: Apache-2.0
module top;
  initial begin
    $display("before_error");
    assert (0);
    $display("after_error");
    $finish;
  end
endmodule
