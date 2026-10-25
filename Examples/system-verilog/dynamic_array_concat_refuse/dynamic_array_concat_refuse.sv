/*
:name: dynamic_array_concat_refuse
:description: A dynamic-array concatenation with a function call remains
  outside the object-free sampled-shape lowering.
:tags: 7.5
:type: simulation
*/
module top;
  int values[];
  function automatic int get_value();
    get_value = 20;
  endfunction
  initial begin
    values = {10, get_value(), 30};
    $display("PASS");
    $finish;
  end
endmodule
