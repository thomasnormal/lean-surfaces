/* The sampled zero-based index is an ordinary integral reduction term. */
module top;
  int values[];
  int total;
  initial begin
    values = new[3]('{10, 20, 30});
    total = values.sum with (item + item.index());
    if (total === 63)
      $display("PASS");
    else
      $display("FAIL %0d", total);
    $finish;
  end
endmodule
