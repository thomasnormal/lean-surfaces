module dimension_queries;
  logic [7:0] vector;
  int integer_value;

  initial begin
    if ($size(vector) == 8 && $high(vector) == 7 &&
        $size(integer_value) == 32 && $high(integer_value) == 31)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
