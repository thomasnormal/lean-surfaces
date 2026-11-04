/*
:name: dynamic_array_concat
:description: IEEE 1800-2023 Section 7.5 -- a finite unpacked
  concatenation samples a dynamic array's size and populates its cells.
:tags: 7.5
:type: simulation
*/
module top;
  initial begin
    int values[];
    values = {10, 20, 30};
    if (values.size() == 3 && values[0] == 10 && values[2] == 30)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
