/* A mailbox try_get with a non-equivalent destination type returns negative. */
module top;
  mailbox box;
  string message;
  int result;
  initial begin
    box = new();
    box.put(42);
    result = box.try_get(message);
    if (result < 0)
      $display("PASS");
    else
      $display("FAIL: expected negative try_get result");
    $finish;
  end
endmodule
