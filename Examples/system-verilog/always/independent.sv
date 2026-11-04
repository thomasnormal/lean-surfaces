// SPDX-License-Identifier: Apache-2.0
// Independent process periods; no extra rearming delay or execution carrier.
module top;
  int fast = 0;
  int slow = 0;
  always #2 fast++;
  always begin #3; slow++; end
  initial begin
    #7;
    $display("independent %0d %0d",fast,slow);
    $finish;
  end
endmodule
