/* A mailbox try_peek with a non-equivalent destination type returns negative. */
module top;
  mailbox box;
  string message;
  int result;
  initial begin
    box = new();
    box.put(42);
    result = box.try_peek(message);
    if (result < 0)
      $display("PASS");
    else
      $display("FAIL: expected negative try_peek result");
    $finish;
  end
endmodule
