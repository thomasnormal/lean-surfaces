/*
:name: dynamic_array_concat_subarrays
:description: IEEE 1800-2023 Section 10.10 -- a finite unpacked
  concatenation contributes fixed scalar-array operands in source order.
:tags: 10.10 unpacked-array-concat dynamic-array
:type: simulation
*/
module top;
  typedef int pair_t[2];
  int values[];

  initial begin
    pair_t middle;
    pair_t tail;
    middle = '{2, 3};
    tail = '{5, 6};
    values = {1, middle, 4, tail};
    if (values.size() == 6 &&
        values[0] == 1 && values[1] == 2 && values[2] == 3 &&
        values[3] == 4 && values[4] == 5 && values[5] == 6)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
