/* semaphore new() defaults to zero keys. */
module top;
  semaphore sem;
  int result;
  initial begin
    sem = new();
    result = sem.try_get(1);
    if (result == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
