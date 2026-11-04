/* An event not triggered in the current time step reports false. */
module top;
  event a;
  event b;
  int first, second;
  initial begin
    b = null;
    first = a.triggered();
    second = b.triggered();
    if (first === 0 && second === 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
