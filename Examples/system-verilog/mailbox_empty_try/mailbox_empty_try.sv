/* Empty mailbox try_get and try_peek are immediate zero results. */
module top;
  mailbox box;
  int value, get_result, peek_result;
  initial begin
    box = new();
    get_result = box.try_get(value);
    peek_result = box.try_peek(value);
    if (get_result == 0 && peek_result == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
