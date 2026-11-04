/* Fixed dimensions remain queryable through an inner dynamic dimension. */
module top;
  int values[3][][5];
  initial begin
    if ($size(values, 1) === 3 &&
        $size(values, 3) === 5 &&
        $unpacked_dimensions(values) === 3)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
