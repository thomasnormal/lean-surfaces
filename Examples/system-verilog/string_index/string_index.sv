/* IEEE 1800-2023 §6.16 string indexing: byte reads and zero bounds. */
module top;
  string s = "abc";
  int first;
  int missing;
  int negative;

  initial begin
    first = s[0];
    missing = s[10];
    negative = s[-1];
    if (first == 8'h61 && missing == 0 && negative == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
