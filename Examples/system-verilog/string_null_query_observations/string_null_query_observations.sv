/* Scalar observations after the IEEE string-character NUL no-op. */
module top;
  initial begin
    string text = "abc";
    text[1] = 0;
    if (text.len() == 3 && text.compare("abc") == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
