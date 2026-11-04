/*
:name: pure_array_query_statements_adapter
:description: Discarded pure fixed-array queries carry no adapter state.
:tags: 7.12
:type: simulation
*/
module top;
  logic [7:0] values [2];
  initial begin
    values[0] = 8'd1;
    values[1] = 8'd2;
    values.min();
    values.max();
    values.unique();
    values.unique_index();
    values.min with (item + 1);
    values.max with (item * 2);
    values.unique with (item + 1);
    values.unique_index with (item + 1);
    values.sum();
    values.product();
    values.and();
    values.or();
    values.xor();
    $display("PASS");
    $finish;
  end
endmodule
