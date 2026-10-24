/* Bare assertion controls have no state in the self-check surface. */
module top;
  initial begin
    $asserton;
    $assertoff;
    $assertkill;
    $display("PASS");
    $finish;
  end
endmodule
