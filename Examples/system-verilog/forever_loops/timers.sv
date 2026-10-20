// SPDX-License-Identifier: Apache-2.0
// A completed body repeats; a waiting body resumes before its next visit.
module top;
  logic [3:0] payload = 4'b1xz0;
  logic [3:0] observed;
  int visits = 0;
  int total = 0;
  int tails = 0;
  initial begin
    #4 payload = 4'bz01x;
    #5 payload = 4'b10xz;
  end
  initial begin
    forever begin
      #2;
      visits++;
      observed = payload;
      $display("visit %0d %b", visits, observed);
      if (visits == 2) continue;
      total += visits;
      if (visits == 4) break;
      #1;
      tails++;
    end
    $display("done %0d %0d %0d %b", visits, total, tails, observed);
    forever begin
      #2;
      break;
    end
    $display("after_break %0d", visits);
    $finish;
  end
endmodule
