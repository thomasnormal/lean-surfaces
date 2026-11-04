/* An unbounded mailbox's literal puts give an exact count at num(). */
module top;
  mailbox box;
  int result;

  initial begin
    box = new();
    box.put(7);
    box.put(8);
    result = box.num();
    if (result === 2)
      $display("PASS");
    else
      $display("FAIL: result=%0d", result);
    $finish;
  end
endmodule
