/* An invalid literal fopen mode is rejected before filesystem access. */
module top;
  int fd;
  initial begin
    fd = $fopen("/tmp/lean_surfaces_invalid_mode", "z");
    if (fd === 0)
      $display("PASS");
    else
      $display("FAIL %0d", fd);
    $finish;
  end
endmodule
