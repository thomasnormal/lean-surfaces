// SPDX-License-Identifier: Apache-2.0
// IEEE 1800-2023 §§12.7.6, 12.8: transfers consume the nearest loop.
module top;
  int visits = 0;
  int total = 0;
  int tails = 0;
  int inner_visits = 0;
  int outer_visits = 0;
  int fresh_total = 0;
  initial begin
    forever begin
      visits++;
      if (visits < 3) continue;
      total += visits;
      if (visits == 5) break;
      tails++;
    end
    $display("transfers %0d %0d %0d", visits, total, tails);
    repeat (3) begin
      outer_visits++;
      forever begin
        inner_visits++;
        break;
      end
    end
    $display("nested %0d %0d", outer_visits, inner_visits);
    visits = 0;
    forever begin
      automatic int cells[0:1] = '{2,3};
      fresh_total += cells[0] + cells[1];
      cells[0] = 99;
      visits++;
      if (visits == 3) break;
    end
    $display("fresh %0d %0d", visits, fresh_total);
    forever begin
      $display("halt %0d", total);
      $finish;
      total = 99;
    end
    $display("unreachable");
  end
endmodule
