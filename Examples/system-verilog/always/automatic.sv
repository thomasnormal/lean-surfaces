// SPDX-License-Identifier: Apache-2.0
// An always-only design starts at time zero and refreshes automatic cells.
module top;
  int total = 0;
  int visits = 0;
  always begin
    automatic logic [3:0] cells[0:1] = '{1,2};
    #2;
    total += cells[0] + cells[1];
    cells[0] = 9;
    visits++;
    if (visits == 3) begin
      $display("automatic %0d %0d",visits,total);
      $finish;
    end
  end
endmodule
