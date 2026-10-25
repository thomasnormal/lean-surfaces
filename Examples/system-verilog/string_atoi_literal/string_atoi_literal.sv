/* atoi scans decimal digits and underscores from a literal string value. */
module top;
  string text;
  int result;

  initial begin
    text = "1_000x";
    result = text.atoi();
    if (result === 1000)
      $display("PASS");
    else
      $display("FAIL: result=%0d", result);
    $finish;
  end
endmodule
