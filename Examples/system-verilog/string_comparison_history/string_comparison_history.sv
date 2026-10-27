/* Source-pure string equality and relational comparisons. */
module top;
  string a;
  string b;
  string c;
  initial begin
    a = "apple";
    b = "apple";
    c = "banana";
    if (a == b && a != c && a < c && a <= b && c > a && c >= b &&
        a === b && a !== c)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
