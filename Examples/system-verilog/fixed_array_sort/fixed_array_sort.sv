/* Fixed unpacked integral arrays sort in source order. */
module top;
  int signed values [0:3];

  initial begin
    values = '{-3, 5, 0, -3};
    values.sort();
    if (values[0] == -3 && values[1] == -3 &&
        values[2] == 0 && values[3] == 5)
      $display("SORT PASS");
    else
      $display("SORT FAIL");
    values.rsort();
    if (values[0] == 5 && values[1] == 0 &&
        values[2] == -3 && values[3] == -3)
      $display("RSORT PASS");
    else
      $display("RSORT FAIL");
    $finish;
  end
endmodule
