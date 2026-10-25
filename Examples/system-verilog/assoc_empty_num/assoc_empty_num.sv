/* Empty associative arrays report zero from num() and size(). */
module top;
  int values[string];
  initial begin
    if (values.num() === 0 && values.size() === 0)
      $display("PASS");
    else
      $display("FAIL: empty associative array count");
    $finish;
  end
endmodule
