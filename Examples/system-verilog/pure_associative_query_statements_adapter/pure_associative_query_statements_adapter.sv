/*
:name: pure_associative_query_statements_adapter
:description: Discarded queries on untouched associative arrays carry no adapter state.
:tags: 7.9
:type: simulation
*/
module top;
  int num_values[string];
  int size_values[string];
  int first_values[string];
  int last_values[int];
  string first_key;
  int last_key;
  initial begin
    num_values.num();
    size_values.size();
    first_values.first(first_key);
    last_values.last(last_key);
    $display("PASS");
    $finish;
  end
endmodule
