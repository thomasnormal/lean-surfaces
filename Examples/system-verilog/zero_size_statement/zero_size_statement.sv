/* Discarded size/len queries on untouched empty storage are zero. */
module top;
  string text;
  int values[$];
  initial begin
    text.len();
    values.size();
    $display("PASS");
    $finish;
  end
endmodule
