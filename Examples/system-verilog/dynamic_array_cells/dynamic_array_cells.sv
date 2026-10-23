/*
:name: dynamic_array_cells
:description: IEEE 1800-2023 Section 7.5 -- constant indexed writes to a
  sampled dynamic array update independent flattened cells.
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
