/*
:name: mixed_array_dimension_adapter
:description: An untouched 2-state mixed array declaration has no flat state.
:tags: 7.4 7.5
:type: simulation
*/
module top;
  initial begin
    bit cells[2][][3];
    $display("PASS");
    $finish;
  end
endmodule
