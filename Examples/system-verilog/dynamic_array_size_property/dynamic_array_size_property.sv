/* §5.13: an empty argument list may be omitted for built-in methods. */
module top;
  int values[];
  int result;
  initial begin
    values = new[7];
    result = values.size;
    if (result === 7)
      $display("PASS");
    else
      $display("FAIL: size=%0d", result);
    $finish;
  end
endmodule
