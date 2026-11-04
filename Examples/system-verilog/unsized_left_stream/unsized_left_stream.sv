/* An unsized left stream uses one-bit chunks for one-bit target leaves. */
module top;
  bit a, b, c, d;
  initial begin
    {<< {a, b, c, d}} = 4'b1010;
    if ({a, b, c, d} === 4'b0101)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
