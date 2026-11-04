/*
:name: pure_zero_size_statements_adapter
:description: Discarded size queries on untouched empty storage carry no adapter state.
:tags: 7.5,6.16
:type: simulation
*/
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
