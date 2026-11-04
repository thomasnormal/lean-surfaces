/* std::semaphore try_get is a nonblocking source-ordered count check. */
module top;
  std::semaphore sem = new(2);
  int first, second, failed;
  initial begin
    // These names are prose, not additional semaphore uses.
    first = sem.try_get(1);
    second = sem.try_get(1);
    failed = sem.try_get(1);
    if (first !== 1 || second !== 1 || failed !== 0)
      $display("FAIL: sem.try_get(1) result");
    else
      $display("PASS");
    $finish;
  end
endmodule
