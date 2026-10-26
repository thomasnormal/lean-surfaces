/* A single dynamic index can dispatch over finite multidimensional cells. */
module top;
  int value [0:1][0:1];
  integer index;
  initial begin
    value[0][1] = 7;
    value[1][1] = 8;
    index = 1;
    if (value[1][index] === 8)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
