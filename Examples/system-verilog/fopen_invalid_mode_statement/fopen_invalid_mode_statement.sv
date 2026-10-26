/* An invalid literal fopen mode is rejected before filesystem access. */
module top;
  initial begin
    $fopen("/tmp/lean_surfaces_invalid_mode_statement", "z");
    $display("PASS");
    $finish;
  end
endmodule
