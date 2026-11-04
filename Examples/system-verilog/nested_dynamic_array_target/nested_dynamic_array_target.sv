/*
:name: nested_dynamic_array_target
:description: dynamic outer array targets with fixed inner dimensions
:tags: 7.4, 10.4
:type: simulation
*/
module top;
  logic [3:0] value[][0:1];
  int outer_index;
  int inner_index;

  initial begin
    value = new[2];
    outer_index = 1;
    inner_index = 0;
    value[outer_index][inner_index] = 4'ha;
    if (value[1][0] === 4'ha)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
