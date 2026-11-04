/* An uninitialized string has length zero. */
module top;
  string text;
  initial begin
    if (text.len() == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
