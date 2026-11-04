/* Exact scalar observations of source-pure ASCII string histories. */
module top;
  initial begin
    string source = "Hello";
    string type_name;
    type_name = $typename(int);
    if (source.len() == 5 && source.substr(1, 3) == "ell" &&
        type_name.len() == 3 && type_name.substr(0, 2) == "int")
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
