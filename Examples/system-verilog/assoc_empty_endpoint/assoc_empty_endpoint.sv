/* Empty associative arrays return zero from first() and last(). */
module top;
  int first_values[string];
  string first_key;
  int last_values[int];
  int last_key;
  int first_result;
  int last_result;
  initial begin
    first_result = first_values.first(first_key);
    last_result = last_values.last(last_key);
    if (first_result === 0 && last_result === 0)
      $display("PASS");
    else
      $display("FAIL: empty associative endpoint");
    $finish;
  end
endmodule
