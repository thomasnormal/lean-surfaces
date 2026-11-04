// SPDX-License-Identifier: Apache-2.0
// The first prefix runs at time zero; each wait retains the unfinished tail.
module top;
  logic [3:0] payload = 4'b1xz0;
  logic [3:0] observed;
  int headers = 0;
  int tails = 0;
  always begin
    headers++;
    observed = payload;
    #2;
    tails++;
  end
  initial begin
    #3 payload = 4'bz01x;
    #4;
    $display("retained %0d %0d %b",headers,tails,observed);
    $finish;
  end
endmodule
