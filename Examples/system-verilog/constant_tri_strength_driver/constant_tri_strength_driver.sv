/* A single explicitly strengthened tri driver has a fixed resolved value. */
module top;
  tri bus;
  assign (strong1, strong0) bus = 1'b1;
  initial begin
    if (bus === 1'b1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
