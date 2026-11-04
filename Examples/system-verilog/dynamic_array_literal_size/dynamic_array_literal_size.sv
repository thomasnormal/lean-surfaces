/* A sampled literal dynamic-array allocation has an exact size. */
module top;
  int values[];
  int result;
  initial begin
    values = new[4];
    result = values.size();
    if (result === 4)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
