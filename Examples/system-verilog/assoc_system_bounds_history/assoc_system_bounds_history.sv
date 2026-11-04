/* System dimension queries observe a finite associative-array history. */
module top;
  int values[int];

  initial begin
    values[-3] = 11;
    values[7] = 22;
    values[2] = 33;
    if ($left(values) == 0 && $low(values) == -3 &&
        $high(values) == 7 && $right(values) == 2147483647 &&
        $increment(values) == -1 && $size(values) == 3)
      $display("PASS1");
    values.delete(7);
    if ($low(values) == -3 && $high(values) == 2 &&
        $size(values) == 2)
      $display("PASS2");
    $finish;
  end
endmodule
