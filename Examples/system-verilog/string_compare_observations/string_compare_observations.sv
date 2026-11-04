/* Exact scalar observations of source-pure string comparison histories. */
module top;
  initial begin
    string source = "Abc";
    string type_name = $typename(int);
    string upper;
    upper = source.toupper();
    if (type_name.compare("int") == 0 &&
        upper.icompare("abc") == 0 &&
        source.compare("Abc") == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
