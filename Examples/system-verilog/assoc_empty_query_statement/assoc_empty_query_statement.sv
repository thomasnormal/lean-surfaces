/* Discarded num/size queries on an untouched associative array are zero. */
module top;
  int values[string];
  initial begin
    values.num();
    values.size();
    $display("PASS");
    $finish;
  end
endmodule
