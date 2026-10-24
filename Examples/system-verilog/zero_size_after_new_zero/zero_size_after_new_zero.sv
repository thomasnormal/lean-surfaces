/* A zero-sized dynamic-array allocation leaves an empty array. */
module top;
  int values[];
  initial begin
    values = new[0];
    if (values.size() == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
