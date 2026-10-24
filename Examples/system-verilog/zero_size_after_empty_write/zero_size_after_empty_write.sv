/* Explicit empty writes preserve the zero size/length of inert storage. */
module top;
  int q[$];
  int values[];
  string text;
  initial begin
    q = {};
    values = {};
    text = "";
    if (q.size() == 0 && values.size() == 0 && text.len() == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
