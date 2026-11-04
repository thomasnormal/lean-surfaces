/* A metadata-only $typename result supports direct and length comparisons. */
module top;
  string s;

  initial begin
    s = $typename(int);
    if ($typename(int) == "int" && s.len() == 3)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
