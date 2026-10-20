// SPDX-License-Identifier: Apache-2.0
// The frontend accepts this null failure action; independent validation refuses it.
module top;
  initial begin
    assert (0) else;
    $display("null_failure");
    $finish;
  end
endmodule
