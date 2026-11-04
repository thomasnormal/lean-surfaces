/* A non-overlapping unpacked-array slice copy reads each source cell once. */
module top;
  int value [0:3];
  initial begin
    value = '{1, 2, 3, 4};
    value[0:1] = value[2:3];
    if (value[0] === 3 && value[1] === 4)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
