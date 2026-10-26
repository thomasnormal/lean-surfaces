/* Empty dynamic-array reductions use the scalar zero result. */
module top;
  int values[];
  int total;
  int product;
  initial begin
    total = values.sum();
    product = values.product();
    if (total === 0 && product === 0)
      $display("PASS");
    else
      $display("FAIL %0d %0d", total, product);
    $finish;
  end
endmodule
