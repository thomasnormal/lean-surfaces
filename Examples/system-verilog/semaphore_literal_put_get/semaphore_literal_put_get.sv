/* Literal semaphore put/get balance, IEEE 1800-2023 §§15.3.2-15.3.3. */
module top;
  semaphore sem;
  int result;
  initial begin
    sem = new(1);
    sem.put(2);
    sem.get(3);
    result = sem.try_get(1);
    if (result == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
