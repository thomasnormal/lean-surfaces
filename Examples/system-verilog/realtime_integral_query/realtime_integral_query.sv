/* `$realtime` is zero when converted to an integral at time zero. */
module top;
  integer now;
  initial begin
    now = $realtime;
    if (now == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
