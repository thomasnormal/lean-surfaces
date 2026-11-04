/* A single dynamic outer index also dispatches through finite cells. */
module top;
  int value [0:1][0:1];
  integer index;
  initial begin
    value[0][1] = 7;
    value[1][1] = 8;
    index = 1;
    value[index][1] = 9;
    if (value[1][1] === 9)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
