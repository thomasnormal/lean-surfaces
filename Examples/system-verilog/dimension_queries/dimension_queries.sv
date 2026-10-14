module dimension_queries;
  logic [7:0] vector;
  int integer_value;

  initial begin
    if ($size(vector) == 8 && $high(vector) == 7 &&
        $left(vector) == 7 && $right(vector) == 0 && $low(vector) == 0 &&
        $increment(vector) == 1 &&
        $size(integer_value) == 32 && $high(integer_value) == 31 &&
        $left(integer_value) == 31 && $right(integer_value) == 0 &&
        $low(integer_value) == 0 && $increment(integer_value) == 1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
