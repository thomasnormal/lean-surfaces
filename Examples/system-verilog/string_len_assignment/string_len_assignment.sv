/* String length follows each source-pure literal assignment. */
module top;
  string text;
  int result;

  initial begin
    text = "hello";
    result = text.len();
    text = "hi!";
    result = result + text.len();
    if (result === 8)
      $display("PASS");
    else
      $display("FAIL: result=%0d", result);
    $finish;
  end
endmodule
