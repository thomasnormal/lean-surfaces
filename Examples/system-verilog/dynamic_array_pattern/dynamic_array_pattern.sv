/*
:name: dynamic_array_pattern
:description: IEEE 1800-2023 Section 10.9 -- a positional assignment
  pattern samples a dynamic array's finite extent.
:tags: 10.9
:type: simulation
*/
module top;
  int values[];
  initial begin
    values = '{10, 20, 30};
    if (values.size() == 3 && values[0] == 10 && values[2] == 30)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
