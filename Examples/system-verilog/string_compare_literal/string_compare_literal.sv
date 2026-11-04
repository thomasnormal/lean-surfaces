/* compare and icompare return normalized ordering values for literals. */
module top;
  string left;
  string right;
  string later;

  initial begin
    left = "Alpha";
    right = "alpha";
    later = "beta";
    if (left.compare(right) === -1 && left.icompare(right) === 0
        && later.compare(right) === 1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
