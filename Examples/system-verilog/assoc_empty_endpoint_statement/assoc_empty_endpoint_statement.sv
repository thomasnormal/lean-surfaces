/* Discarded first/last queries on untouched associative arrays return zero. */
module top;
  int first_values[string];
  string first_key;
  int last_values[int];
  int last_key;
  initial begin
    first_values.first(first_key);
    last_values.last(last_key);
    $display("PASS");
    $finish;
  end
endmodule
