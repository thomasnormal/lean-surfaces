/* `$stime` is zero in the time-zero self-check slice. */
module top;
  integer now;
  initial begin
    now = $stime;
    if (now == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
