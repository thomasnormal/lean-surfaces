/* $bits determines a size without evaluating its expression argument. */
module top;
  int counter;
  initial begin
    $bits(counter++);
    if (counter == 0)
      $display("PASS");
    else
      $display("FAIL: $bits evaluated its argument");
    $finish;
  end
endmodule
