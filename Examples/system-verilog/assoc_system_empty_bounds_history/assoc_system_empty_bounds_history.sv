/* Empty associative arrays return unknown low/high bounds. */
module top;
  int values[int];
  logic [31:0] low_value, high_value;

  initial begin
    low_value = $low(values);
    high_value = $high(values);
    if ($isunknown(low_value) && $isunknown(high_value) &&
        $size(values) == 0)
      $display("PASS");
    $finish;
  end
endmodule
