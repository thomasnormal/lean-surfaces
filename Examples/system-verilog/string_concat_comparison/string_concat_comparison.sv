/* A named ASCII string concatenation can be compared and displayed exactly. */
module top;
  string a, b, result;

  initial begin
    a = "Hello";
    b = " World";
    result = {a, b};
    if (result == "Hello World")
      $display("%s", result);
    else
      $display("FAIL");
    $finish;
  end
endmodule
