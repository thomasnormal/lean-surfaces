/* System $size observes a finite integral-key associative-array history. */
module top;
  initial begin
    int values[int];
    if ($size(values) != 0)
      $display("FAIL0");
    values[10] = 1;
    values[20] = 2;
    values[10] += 3;
    if ($size(values) == 2 && values[10] == 4 && values[20] == 2)
      $display("PASS1");
    values.delete(10);
    if ($size(values) == 1 && values[10] == 0)
      $display("PASS2");
    values.delete();
    if ($size(values) == 0)
      $display("PASS3");
    $finish;
  end
endmodule
