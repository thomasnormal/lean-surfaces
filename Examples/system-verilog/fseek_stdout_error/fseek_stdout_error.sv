/* Seeking the predefined stdout descriptor reports the standard error code. */
module top;
  int code;
  initial begin
    code = $fseek(32'h8000_0001, 0, 0);
    if (code == -1)
      $display("PASS");
    else
      $display("FAIL: code=%0d", code);
    $finish;
  end
endmodule
