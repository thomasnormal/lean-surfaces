/* A metadata-only $typename result can feed a pure string assignment. */
module top;
  string s;

  initial begin
    s = $typename(int);
    if (s == "int")
      $display("PASS");
    else
      $display("FAIL: typename=%s", s);
    $finish;
  end
endmodule
