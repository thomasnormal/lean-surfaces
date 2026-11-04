/* Uninitialized queues and dynamic arrays have size zero. */
module top;
  int q[$];
  int values[];
  initial begin
    if (q.size() == 0 && values.size() == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
