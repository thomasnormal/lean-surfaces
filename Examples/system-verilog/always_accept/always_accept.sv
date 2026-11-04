// SPDX-License-Identifier: Apache-2.0
// A plain always process repeats through the timed scheduler until it stops.
module top;
  int visits = 0;
  always begin
    #1;
    visits++;
    if (visits == 2) begin
      $display("ALWAYS PASS");
      $finish;
    end
  end
endmodule
