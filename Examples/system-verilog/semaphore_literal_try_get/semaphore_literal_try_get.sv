/* Literal semaphore try_get state sequence, IEEE 1800-2023 §15.3.4. */
module top;
  semaphore sem;
  int first, second, failed;
  initial begin
    sem = new(3);
    first = sem.try_get(2);
    second = sem.try_get(1);
    failed = sem.try_get(1);
    if (first > 0 && second > 0 && failed == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
