/* Empty dynamic arrays and strings have zero runtime bit width. */
module top;
  int dyn[];
  string text = "";
  int result;
  initial begin
    if ($bits(dyn) === 0 && $bits(text) === 0)
      $display("PASS");
    else
      $display("FAIL: expected empty bit widths");
    $finish;
  end
endmodule
