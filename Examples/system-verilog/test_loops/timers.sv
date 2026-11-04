module top;
  logic [3:0] guard = 4'b1x00;
  integer visits = 0, tails = 0;
  initial begin
    while (guard) begin
      #1;
      visits++;
      if (visits == 1) continue;
      guard = 4'bx0z0;
    end
    $display("while_wait %0d", visits);
    do begin
      #1;
      tails++;
      if (tails == 1) continue;
      break;
    end while (1);
    $display("do_wait %0d", tails);
    $finish;
  end
endmodule
