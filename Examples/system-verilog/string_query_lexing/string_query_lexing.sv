/* Receiver names in comments must not count as runtime observations:
   s.len() and s.getc(99) are prose here. */
module top;
  string s;
  initial begin
    // The quoted \n escape is followed by a consumed backslash-newline.
    s = "AB.\n\
CD";
    // This comment also mentions s.len() and s.getc(100).
    if (s.len() == 6 &&
        s.getc(0) == 8'd65 &&
        s.getc(3) == 8'd10 &&
        s.getc(4) == 8'd67)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
