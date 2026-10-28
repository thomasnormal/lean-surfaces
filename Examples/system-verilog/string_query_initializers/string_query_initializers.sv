/* Source-pure string query initializers replay as exact ASCII values. */
module top;
  initial begin
    string source = "Hello";
    string upper = source.toupper();
    string lower = source.tolower();
    string middle = source.substr(1, 3);
    string formatted = $sformatf("Value: %0d", 42);
    if (upper == "HELLO" && lower == "hello" && middle == "ell" &&
        formatted == "Value: 42")
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
