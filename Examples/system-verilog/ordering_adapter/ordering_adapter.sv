/* Fixed-array ordering methods lower to the existing flat-cell state. */
// PASS
module top;
  int signed values [0:3];
  initial begin
    values = '{5, 1, 3, 2};
    values.sort();
    values.rsort();
    if (values[0] == 5 && values[1] == 3 &&
        values[2] == 2 && values[3] == 1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
