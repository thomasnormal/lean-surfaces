/* A literal tri driver has the same fixed value as a literal wire driver. */
module top;
  tri bus;
  assign bus = 1'b1;
  initial begin
    if (bus === 1'b1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
