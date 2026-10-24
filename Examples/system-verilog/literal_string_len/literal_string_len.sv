/* A literal string's unchanged length is an integral fact. */
module top;
  initial begin
    string greeting = "hello";
    string empty = "";
    if (greeting.len() == 5 && empty.len() == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
