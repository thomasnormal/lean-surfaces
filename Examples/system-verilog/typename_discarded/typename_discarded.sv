/* $typename determines a type without evaluating its expression argument. */
module top;
  int counter;
  initial begin
    $typename(counter++);
    if (counter == 0)
      $display("PASS");
    else
      $display("FAIL: $typename evaluated its argument");
    $finish;
  end
endmodule
