/* Discarded finite associative-array exists calls are pure observations. */
module top;
  int score[int];

  initial begin
    score[1] = 40;
    score.exists(1);
    if (score.exists(1) && score[1] == 40)
      $display("PASS");
    else
      $display("FAIL: discarded exists changed state");
    $finish;
  end
endmodule
