/* Current bounds and declared rank for dynamic arrays and empty queues. */
module top;
  int values[];
  int q[$];

  initial begin
    if ($left(values) != 0 || $right(values) != -1 ||
        $size(values) != 0 || $increment(values) != -1 ||
        $dimensions(values) != 2 || $unpacked_dimensions(values) != 1)
      $finish;

    values = new[4];
    if ($left(values) != 0 || $right(values) != 3 ||
        $low(values) != 0 || $high(values) != 3 ||
        $size(values) != 4 || $increment(values) != -1)
      $finish;

    if ($left(q) != 0 || $right(q) != -1 || $size(q) != 0 ||
        $increment(q) != -1 || $dimensions(q) != 2 ||
        $unpacked_dimensions(q) != 1)
      $finish;

    $display("PASS");
    $finish;
  end
endmodule
