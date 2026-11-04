/*
:name: pure_dimension_query_statements_adapter
:description: Discarded fixed dimension queries carry no adapter state.
:tags: 20.7
:type: simulation
*/
module top;
  logic [7:0] value;
  initial begin
    $size(value);
    $high(value);
    $left(value);
    $right(value);
    $low(value);
    $increment(value);
    $dimensions(value);
    $unpacked_dimensions(value);
    $display("PASS");
    $finish;
  end
endmodule
