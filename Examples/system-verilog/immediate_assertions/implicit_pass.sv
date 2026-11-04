// SPDX-License-Identifier: Apache-2.0
module top;
  initial begin
    assert (1);
    assume (1);
    cover (0);
    $display("implicit_pass");
    $finish;
  end
endmodule
