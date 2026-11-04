/*
:name: dynamic_extent_adapter
:description: A constant dynamic-array extent lowers to flat self-check cells.
:tags: 7.5
:type: simulation
*/
module top;
  initial begin
    int values[];
    values = new[3];
    values[0] = 10;
    values[1] = 20;
    values[2] = 30;
    if (values[0] == 10 && values[2] == 30)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
