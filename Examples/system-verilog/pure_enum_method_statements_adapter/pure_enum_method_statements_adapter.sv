/*
:name: pure_enum_method_statements_adapter
:description: Discarded source-pure enum methods carry no adapter state.
:tags: 6.19
:type: simulation
*/
module top;
  typedef enum logic [1:0] { A = 0, B = 1, C = 2 } E;
  E value;
  initial begin
    value = B;
    value.name();
    value.first();
    value.last();
    value.num();
    value.next();
    value.prev();
    $display("PASS");
    $finish;
  end
endmodule
