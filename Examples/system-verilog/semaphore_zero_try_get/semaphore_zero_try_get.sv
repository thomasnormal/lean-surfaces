module top;
  semaphore sem;
  int result;

  initial begin
    sem = new(1);
    result = sem.try_get(0);
    if (result > 0)
      $display("PASS");
    else
      $display("FAIL: result=%0d", result);
    $finish;
  end
endmodule
